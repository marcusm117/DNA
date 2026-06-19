# License: Apache 2.0
# pylint: disable=R0902,R0912


# Standard Library Modules
import argparse
import asyncio
import logging
import os
import time
from pprint import pprint
from typing import Any, Literal

# External Modules
import aioboto3
import boto3
from botocore.config import Config as BotocoreConfig
from botocore.exceptions import ClientError
from dotenv import load_dotenv
from typing_extensions import TypedDict, Unpack

# Internal Modules
from .type_defs import BedrockRole, Content, Messages


# Load environment variables from the .env file
load_dotenv(dotenv_path="../.env")

# Setup logger for this module
logger = logging.getLogger(__name__)


# Constants
# See the doc below for all model ids
# https://docs.aws.amazon.com/bedrock/latest/userguide/models-supported.html
BEDROCK_CLAUDE_MODEL_LIST = [
    "us.anthropic.claude-3-5-haiku-20241022-v1:0",
    "us.anthropic.claude-3-7-sonnet-20250219-v1:0",
    "us.anthropic.claude-sonnet-4-20250514-v1:0",
    "us.anthropic.claude-opus-4-20250514-v1:0",
    "us.anthropic.claude-opus-4-1-20250805-v1:0",
    # Claude Opus 4.8: bare ID (no date, no ":0"); temperature is deprecated and must be omitted.
    "us.anthropic.claude-opus-4-8",
]
BEDROCK_CLAUDE_THINKING_MODEL_LIST = [
    "us.anthropic.claude-3-7-sonnet-20250219-v1:0-thinking",
    "us.anthropic.claude-sonnet-4-20250514-v1:0-thinking",
    "us.anthropic.claude-opus-4-1-20250805-v1:0-thinking",
    "us.anthropic.claude-opus-4-20250514-v1:0-thinking",
    # Claude Opus 4.8: one model ID per effort level (adaptive thinking + output_config effort).
    "us.anthropic.claude-opus-4-8-thinking-low",
    "us.anthropic.claude-opus-4-8-thinking-medium",
    "us.anthropic.claude-opus-4-8-thinking-high",
    "us.anthropic.claude-opus-4-8-thinking-xhigh",
    "us.anthropic.claude-opus-4-8-thinking-max",
]

# Claude Opus 4.8 base model ID. Variants extend this with a "-thinking-<effort>" suffix.
# 4.8 differs from earlier Bedrock Claude models: temperature is deprecated (must be omitted),
# and extended thinking uses {"type": "adaptive"} + output_config.effort instead of
# {"type": "enabled", "budget_tokens": N}.
BEDROCK_CLAUDE_OPUS_4_8_ID = "us.anthropic.claude-opus-4-8"


class BedrockConfig(TypedDict, total=False):
    """Configuration for Bedrock model parameters.

    Reference: http://boto3.amazonaws.com/v1/documentation/api/latest/reference/services/bedrock-runtime/client/converse.html
    """

    # Core parameters
    max_tokens: int
    temperature: float
    top_p: float
    stop_sequences: list[str]

    # Advanced parameters
    streaming: bool
    additional_args: dict[str, Any]
    additional_request_fields: dict[str, Any]
    additional_response_field_paths: list[str]

    # Caching parameters
    cache_prompt: str
    cache_tools: str

    # Guardrail parameters
    guardrail_id: str
    guardrail_trace: Literal["enabled", "disabled", "enabled_full"]
    guardrail_stream_processing_mode: Literal["sync", "async"]
    guardrail_version: str
    guardrail_redact_input: bool
    guardrail_redact_input_message: str
    guardrail_redact_output: bool
    guardrail_redact_output_message: str

    # Anthropic-specific parameters
    claude_thinking_type: str
    claude_thinking_budget_tokens: int


class BedrockModel:
    def __init__(
        self,
        *,  # keyword-only arguments
        aws_access_key_id: str | None = None,
        aws_secret_access_key: str | None = None,
        aws_session_token: str | None = None,
        region_name: str | None = None,
        boto_client_config: BotocoreConfig | None = None,
        model_id: str,
        **inference_config: Unpack[BedrockConfig],
    ):
        """Initialize provider instance.

        Args:
            region_name: AWS region to use for the Bedrock service.
                Defaults to the AWS_REGION environment variable if set, or "us-east-1" if not set.
            boto_client_config: Configuration to use when creating the Bedrock-Runtime Boto Client.
            model_id: The Bedrock model ID (e.g., "us.anthropic.claude-sonnet-4-20250514-v1:0")
            **inference_config: Configuration options for the Bedrock model.
        """
        # Construct session_args from `aws_access_key_id`, `aws_secret_access_key`, `aws_session_token`, and `region_name`
        self.session_args = {
            "aws_access_key_id": aws_access_key_id or os.getenv("AWS_ACCESS_KEY_ID"),
            "aws_secret_access_key": aws_secret_access_key or os.getenv("AWS_SECRET_ACCESS_KEY"),
            "aws_session_token": aws_session_token or os.getenv("AWS_SESSION_TOKEN"),
            "region_name": region_name or os.getenv("AWS_REGION") or "us-east-1",
        }

        # Initialize `model_id`, `messages`, and `system_prompt`
        self.model_id = model_id
        self.messages: Messages = []
        self.system_prompt: str = ""

        # Update `inference_config` with user-provided config
        self.inference_config = BedrockConfig()
        self.inference_config.update(inference_config)

        logger.debug("inference_config=<%s> | initializing", self.inference_config)

        # Lazy session initialization
        self._session: boto3.Session | None = None
        self._async_session: aioboto3.Session | None = None

        # Construct client arguments
        self.client_args = {
            "service_name": "bedrock-runtime",
            "config": boto_client_config
            or BotocoreConfig(
                connect_timeout=60,
                read_timeout=600,
                max_pool_connections=20,
                retries={
                    "max_attempts": 10,
                    "mode": "standard",
                },
            ),
        }

    @property
    def session(self) -> boto3.Session:
        if self._session is None:
            self._session = boto3.Session(**self.session_args)
            logger.info("Bedrock session initialized")
        return self._session

    @property
    def async_session(self) -> aioboto3.Session:
        if self._async_session is None:
            self._async_session = aioboto3.Session(**self.session_args)
            logger.info("Bedrock ASYNC session initialized")
        return self._async_session

    def update_config(self, **inference_config: Unpack[BedrockConfig]) -> None:
        """Update the Bedrock Model configuration with the provided arguments.

        Args:
            **inference_config: Configuration overrides.
        """
        self.inference_config.update(inference_config)

    def get_config(self) -> BedrockConfig:
        """Get the current Bedrock Model configuration.

        Returns:
            The Bedrock model configuration.
        """
        return self.inference_config

    def add_message(self, role: BedrockRole, content: str | Content) -> None:
        """Add a message to the conversation.

        Args:
            role: The role of the message ("user", "assistant")
            content: The content of the message (string or list of content blocks)
        """
        # Convert string content to proper Bedrock format
        if isinstance(content, str):
            content_blocks = [{"text": content}]
        # If content is already a list of dicts, don't need to do anything
        else:
            content_blocks = content

        self.messages.append({"role": role, "content": content_blocks})

    def add_messages(self, messages: Messages) -> None:
        """Add a list of messages to the conversation.

        Args:
            messages: List of message objects to be added to the conversation.
        """
        self.messages.extend(messages)

    def _estimate_token_count(self, text: str) -> int:
        """Estimate token count for text (rough approximation: 1 token ≈ 5 characters)

        Minus 50 tokens so that we don't overestimate the token count.
        """
        return (len(text) // 5) - 50

    def _get_total_content_tokens(self, messages: Messages, system_prompt: str = "") -> int:
        """Calculate total token count for all message content and system prompt"""
        total_tokens = self._estimate_token_count(system_prompt) if system_prompt else 0

        for message in messages:
            for content_item in message.get("content", []):
                if content_item.get("text"):
                    total_tokens += self._estimate_token_count(content_item["text"])
                # Note: We don't count image tokens as they don't contribute to text caching

        return total_tokens

    def format_request(
        self,
        system_prompt: str | None = None,
        messages: Messages | None = None,
    ) -> dict[str, Any]:
        """Format a Bedrock converse request.

        Args:
            system_prompt: System prompt to provide context to the model.
                          If None, extracts from messages.
            messages: List of message objects to be processed by the model.
                      If None, uses internally stored messages.

        Returns:
            A Bedrock converse request.
        """
        # Use internal system prompt if not provided
        if system_prompt is None:
            system_prompt = self.system_prompt
        # Use internal messages if not provided
        if messages is None:
            messages = self.messages

        # Handling Claude Opus 4.8 thinking models (adaptive thinking + effort level).
        # The effort level is encoded as the suffix after "-thinking-" in the model ID
        # (e.g. "...-thinking-high" -> effort "high"). 4.8 uses a different thinking shape
        # than earlier models and must NOT receive a temperature (handled in the pipeline init).
        if self.model_id.startswith(BEDROCK_CLAUDE_OPUS_4_8_ID) and "-thinking-" in self.model_id:
            effort = self.model_id.rsplit("-thinking-", 1)[1]
            self.inference_config["additional_request_fields"] = {
                "thinking": {"type": "adaptive"},
                "output_config": {"effort": effort},
            }
        # Handling Anthropic reasoning/thinking models
        elif self.model_id in BEDROCK_CLAUDE_THINKING_MODEL_LIST:
            self.inference_config["claude_thinking_type"] = self.inference_config.get("claude_thinking_type", "enabled")
            self.inference_config["claude_thinking_budget_tokens"] = self.inference_config.get("claude_thinking_budget_tokens", 16_384)

            # Check if thinking is enabled
            if self.inference_config["claude_thinking_type"] != "enabled":
                print(f"⚠️  Warning: {self.model_id} is a reasoning model, but you have disabled thinking, setting claude_thinking_type to 'enabled'")
                self.inference_config["claude_thinking_type"] = "enabled"

            # Budget can't be less than 1024, see: https://docs.aws.amazon.com/bedrock/latest/userguide/claude-messages-extended-thinking.html
            if self.inference_config["claude_thinking_budget_tokens"] < 1024:
                print(
                    f"⚠️  Warning: {self.model_id} is a reasoning model, "
                    f"but you have set a budget of {self.inference_config['claude_thinking_budget_tokens']} tokens, "
                    "setting it to the minimum 1024"
                )
                self.inference_config["claude_thinking_budget_tokens"] = 1024

            # Add reasoning/thinking parameters to the request
            self.inference_config["additional_request_fields"] = {
                "thinking": {
                    "type": self.inference_config["claude_thinking_type"],
                    "budget_tokens": self.inference_config["claude_thinking_budget_tokens"],
                }
            }

        # If `cache_prompt` is configured, check if we have enough tokens before adding cache points
        cache_prompt_type = self.inference_config.get("cache_prompt")
        cache_system_prompt = False
        if cache_prompt_type:
            # Determine minimum tokens required based on model
            min_tokens_required = 2048  # Default for Claude 3.5 Haiku
            if any(model in self.model_id for model in ["opus", "sonnet"]):
                min_tokens_required = 1024

            # Decide whether to cache the system prompt
            if system_prompt:
                total_tokens_system_prompt = self._estimate_token_count(system_prompt)
                if total_tokens_system_prompt > min_tokens_required:
                    cache_system_prompt = True
                    logger.info("Added cache point to the system prompt for %s", self.model_id)
                    print(f"Added cache point to the system prompt for {self.model_id}")
                else:
                    logger.info(
                        "Skipping cache point addition - insufficient tokens: %d < %d for %s",
                        total_tokens_system_prompt,
                        min_tokens_required,
                        self.model_id,
                    )
                    print(
                        f"Skipping cache point addition - insufficient tokens: {total_tokens_system_prompt} < "
                        f"{min_tokens_required} for {self.model_id}"
                    )

            # Find the last user message before the first assistant message
            # If no assistant messages, use the last message
            last_index = len(messages) - 1  # Default to last message
            for i, message in enumerate(messages):
                if message["role"] == "assistant":
                    last_index = i - 1
                    break

            # Calculate total token count of the messages before the first assistant message
            total_tokens = self._get_total_content_tokens(messages[: last_index + 1])

            # Only add cache points if we have enough tokens
            if total_tokens > min_tokens_required:
                # Add cache point as a separate content item
                messages[last_index]["content"].append({"cachePoint": {"type": cache_prompt_type}})
                logger.info("Added cache point to the last user message before any assistant message")
                print(f"Added cache point to the last user message before any assistant message for {self.model_id}")
            else:
                logger.info("Skipping cache point addition - insufficient tokens: %d < %d for %s", total_tokens, min_tokens_required, self.model_id)
                print(f"Skipping cache point addition - insufficient tokens: {total_tokens} < {min_tokens_required} for {self.model_id}")

        # Strip the thinking suffix to obtain the bare model ID sent to converse().
        # For 4.8 the suffix is the full "-thinking-<effort>" (e.g. "...-thinking-high");
        # for earlier models it is just "-thinking".
        if self.model_id.startswith(BEDROCK_CLAUDE_OPUS_4_8_ID):
            converse_model_id = BEDROCK_CLAUDE_OPUS_4_8_ID
        elif self.model_id in BEDROCK_CLAUDE_THINKING_MODEL_LIST:
            converse_model_id = self.model_id.replace("-thinking", "")
        else:
            converse_model_id = self.model_id

        return {
            "modelId": converse_model_id,
            "messages": messages,
            "system": [
                *([{"text": system_prompt}] if system_prompt else []),
                # if no system prompt, we don't add cache point even if `cache_prompt_type` is set
                *([{"cachePoint": {"type": cache_prompt_type}}] if (cache_prompt_type and system_prompt and cache_system_prompt) else []),
            ],
            **(
                {"additionalModelRequestFields": self.inference_config.get("additional_request_fields")}
                if self.inference_config.get("additional_request_fields")
                else {}
            ),
            **(
                {"additionalModelResponseFieldPaths": self.inference_config.get("additional_response_field_paths")}
                if self.inference_config.get("additional_response_field_paths")
                else {}
            ),
            **(
                {
                    "guardrailConfig": {
                        "guardrailIdentifier": self.inference_config.get("guardrail_id"),
                        "guardrailVersion": self.inference_config.get("guardrail_version"),
                        "trace": self.inference_config.get("guardrail_trace", "enabled"),
                        **(
                            {"streamProcessingMode": self.inference_config.get("guardrail_stream_processing_mode")}
                            if self.inference_config.get("guardrail_stream_processing_mode")
                            else {}
                        ),
                    }
                }
                if self.inference_config.get("guardrail_id") and self.inference_config.get("guardrail_version")
                else {}
            ),
            "inferenceConfig": {
                key: value
                for key, value in [
                    ("maxTokens", self.inference_config.get("max_tokens")),
                    ("temperature", self.inference_config.get("temperature")),
                    ("topP", self.inference_config.get("top_p")),
                    ("stopSequences", self.inference_config.get("stop_sequences")),
                ]
                if value is not None
            },
            **(self.inference_config.get("additional_args", {}) or {}),
        }

    def extract_response(self, response: dict[str, Any]) -> tuple[str, dict, list[str]]:
        """Extract response text and usage from Bedrock response.

        Args:
            response: The response from Bedrock model.

        Returns:
            A tuple of (response_text, usage_dict, reasoning_summary_list).
        """
        # Extract response text
        response_text = ""
        if "output" in response and "message" in response["output"]:
            content = response["output"]["message"].get("content", [])
            for content_item in content:
                if content_item.get("text"):
                    response_text = content_item["text"]
                    break

        # Extract token usage
        usage = response.get("usage", {})

        # Extract reasoning summary
        # https://boto3.amazonaws.com/v1/documentation/api/latest/reference/services/bedrock-runtime/client/converse.html
        # https://docs.aws.amazon.com/bedrock/latest/userguide/claude-messages-thinking-differences.html
        reasoning_summary_list: list[str] = []
        message = response.get("output", {}).get("message", {})
        # Get all reasoning blocks
        for content_block in message.get("content", []):
            reasoning_content = content_block.get("reasoningContent", {})
            if not reasoning_content:
                continue
            reasoning_text = reasoning_content.get("reasoningText", {})
            # the "text" field contains the full reasoning for Claude 3.7, but only the summary for Claude 4 and beyond
            if isinstance(reasoning_text, dict) and reasoning_text.get("text"):
                reasoning_summary_list.append(reasoning_text["text"])

        return response_text, usage, reasoning_summary_list

    def get_response(
        self,
        client: Any,
        system_prompt: str | None = None,
        messages: Messages | None = None,
    ) -> tuple[str, dict, list[str], Any]:
        # Retry until success
        while True:
            response = None  # Initialize response to avoid UnboundLocalError
            try:
                request: dict[str, Any] = self.format_request(system_prompt, messages)
                logger.debug("request=<%s> | making converse call", request)

                response = client.converse(**request)
                logger.debug("response=<%s> | received", response)

                response_text, usage, reasoning_summary_list = self.extract_response(dict(response))
                if not response_text:
                    print("⚠️  Warning: response_text is empty, retrying...")
                    continue

                return response_text, usage, reasoning_summary_list, dict(response)

            # Handle Bedrock Client errors first
            except ClientError as e:
                error_str = str(e)
                logger.error("ClientError during converse call: %s", error_str)
                print(f"⚠️  ClientError occurred: {error_str}, retrying...")
                # Check if it's a ThrottlingException, and wait 30 seconds if so
                if "ThrottlingException" in error_str:
                    wait_time = 30
                    logger.info("ThrottlingException detected, waiting %d seconds before retry", wait_time)
                    print(f"🕒 ThrottlingException detected, waiting {wait_time} seconds before retry...")
                    time.sleep(wait_time)
                continue

            # Handle all other errors
            except Exception as e:
                print(f"⚠️  Unexpected error occurred: {e}, got the response: {response}")
                print("Retrying...")
                continue

    async def get_response_async(
        self,
        async_client: aioboto3.Session.client,
        system_prompt: str | None = None,
        messages: Messages | None = None,
    ) -> tuple[str, dict, list[str], Any]:
        # Retry until success
        while True:
            response = None  # Initialize response to avoid UnboundLocalError
            try:
                request: dict[str, Any] = self.format_request(system_prompt, messages)
                logger.debug("request=<%s> | making ASYNC converse call", request)

                response = await async_client.converse(**request)
                logger.debug("response=<%s> | received", response)

                response_text, usage, reasoning_summary_list = self.extract_response(dict(response))
                if not response_text:
                    print("⚠️  Warning: response_text is empty, retrying...")
                    continue

                return response_text, usage, reasoning_summary_list, dict(response)

            # Handle Bedrock Client errors first
            except ClientError as e:
                error_str = str(e)
                logger.error("ClientError during ASYNC converse call: %s", error_str)
                print(f"⚠️  ClientError occurred: {error_str}, retrying...")
                # Check if it's a ThrottlingException and wait 30 seconds
                if "ThrottlingException" in error_str:
                    wait_time = 30
                    logger.info("ThrottlingException detected, waiting %d seconds before retry", wait_time)
                    print(f"🕒 ThrottlingException detected, waiting {wait_time} seconds before retry...")
                    await asyncio.sleep(wait_time)
                continue

            # Handle all other errors
            except Exception as e:
                logger.error("Unexpected error during ASYNC converse call: %s", e)
                print(f"⚠️  Unexpected error occurred: {e}, got the response: {response}")
                print("Retrying...")
                continue


# EXAMPLE USAGE:
# python inference_bedrock.py
async def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--region", type=str, default="us-west-2")
    parser.add_argument("--model_id", type=str, default=BEDROCK_CLAUDE_MODEL_LIST[1])
    parser.add_argument("--max_tokens", type=int, default=1024)
    parser.add_argument("--temperature", type=float, default=0.1)
    args = parser.parse_args()

    # Create a BedrockModel instance
    bedrock_model = BedrockModel(
        region_name=args.region,
        model_id=args.model_id,
        max_tokens=args.max_tokens,
        temperature=args.temperature,
        cache_prompt="default",
    )

    print("========================== Client ==========================")
    print(f"Region: {bedrock_model.session_args['region_name']}")
    print(f"Service Name: {bedrock_model.client_args['service_name']}")
    print(f"Client Config: {bedrock_model.client_args['config'].__dict__}")
    print("========================== Model ==========================")
    print(f"Model ID: {bedrock_model.model_id}")
    print(f"Model Config: {bedrock_model.get_config()}")

    # Add a simple list of messages
    # For prompt caching, see: https://docs.aws.amazon.com/bedrock/latest/userguide/prompt-caching.html
    bedrock_model.system_prompt = (
        "Please answer all questions in detail. "
        "Claude 4 Opus, Claude 4 Sonnet, Claude 3.7 Sonnet, Claude 3.5 Sonnet require a minimum of 1024 tokens per cache checkpoint. "
        "Claude 3.5 Haiku requires a minimum of 2048 tokens per cache checkpoint. "
        "This is a " + "very " * 1024 + "long system prompt to test prompt caching."
    )
    bedrock_model.add_message(
        "user", "Which model and version are you? When are you created? When is your knowledge cut-off date? What is the current date?"
    )
    print(bedrock_model.system_prompt)

    # Test sync client
    print("========================== Sync Test ==========================")
    # Create a client using the sync session
    client = bedrock_model.session.client(**bedrock_model.client_args)
    response_text, usage, reasoning_summary_list, _ = bedrock_model.get_response(client)
    print("-------------------------- Messages --------------------------")
    pprint(bedrock_model.messages)
    print("-------------------------- Response --------------------------")
    print(response_text)
    print("-------------------------- Usage --------------------------")
    print(usage)
    print("-------------------------- Reasoning Summary --------------------------")
    print(reasoning_summary_list)
    print("========================== Sync End ==========================")

    # Test async client
    print("========================== Async Test ==========================")
    # Create an async client using the async session
    async with bedrock_model.async_session.client(**bedrock_model.client_args) as async_client:
        response_text, usage, reasoning_summary_list, _ = await bedrock_model.get_response_async(async_client)
    print("-------------------------- Async Messages --------------------------")
    pprint(bedrock_model.messages)
    print("-------------------------- Response --------------------------")
    print(response_text)
    print("-------------------------- Usage --------------------------")
    print(usage)
    print("-------------------------- Reasoning Summary --------------------------")
    print(reasoning_summary_list)
    print("========================== Async End ==========================")


if __name__ == "__main__":
    asyncio.run(main())
