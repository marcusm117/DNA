# License: Apache 2.0
# pylint: disable=R0912


# Standard Library Modules
import argparse
import asyncio
import logging
import os
from pprint import pprint
from typing import Any, Literal

# External Modules
from dotenv import load_dotenv
from openai import OpenAI, AsyncOpenAI, OpenAIError
from typing_extensions import TypedDict, Unpack

# Internal Modules
from .type_defs import OpenAIRole, Content, Messages


# Load environment variables from the .env file
load_dotenv(dotenv_path="../.env")

# Setup logger for this module
logger = logging.getLogger(__name__)


# Constants
# See the doc below for all model ids
# https://platform.openai.com/docs/models
OPENAI_GPT_MODEL_LIST = [
    "gpt-4.1-nano-2025-04-14",
    "gpt-4.1-mini-2025-04-14",
    "gpt-4.1-2025-04-14",
]
OPENAI_O_MODEL_LIST = [
    "o4-mini-2025-04-16",
    "o3-mini-2025-01-31",
    "o3-2025-04-16",
    "o4-mini",
    "o3-mini",
    "o3",
]
OPENAI_GPT5_MODEL_LIST = [
    "gpt-5-nano-2025-08-07",
    "gpt-5-mini-2025-08-07",
    "gpt-5-2025-08-07",
]


class OpenAIConfig(TypedDict, total=False):
    """Configuration for OpenAI model parameters.

    Reference: https://platform.openai.com/docs/api-reference/responses/create
    """

    # Core parameters
    temperature: float
    max_output_tokens: int
    top_p: float

    # Token generation parameters
    frequency_penalty: float
    presence_penalty: float
    logit_bias: dict[str, int]
    logprobs: bool
    top_logprobs: int
    n: int
    stop: list[str]

    # Caching parameters
    prompt_cache_key: str

    # Streaming and response parameters
    stream: bool
    stream_options: dict[str, Any]

    # Response API specific parameters
    store: bool
    metadata: dict[str, str]
    user: str
    previous_response_id: str

    # Tools and function calling
    tools: list[dict[str, Any]]
    tool_choice: str | dict[str, Any]
    parallel_tool_calls: bool

    # Response format
    response_format: dict[str, Any]

    # Reasoning parameters ("minimal" only works for gpt-5 models), see:
    # https://cookbook.openai.com/examples/gpt-5/gpt-5_new_params_and_tools
    reasoning_effort: Literal["minimal", "low", "medium", "high"]
    reasoning_summary: Literal["auto", "concise", "detailed"]

    # Verbosity parameters (gpt-5 models only), see:
    # https://cookbook.openai.com/examples/gpt-5/gpt-5_new_params_and_tools
    verbosity: Literal["low", "medium", "high"]


class OpenAIModel:
    def __init__(
        self,
        *,  # keyword-only arguments
        base_url: str | None = None,
        api_key: str | None = None,
        model_id: str,
        **inference_config: Unpack[OpenAIConfig],
    ) -> None:
        """Initialize provider instance.

        Args:
            model_id: The OpenAI model ID (e.g., "gpt-4.1-2025-04-14")
            **inference_config: Configuration options for the OpenAI model.
        """
        # Initialize `base_url` and `api_key`
        self.base_url = base_url or os.getenv("OPENAI_BASE_URL") or "https://api.openai.com/v1"
        self.api_key = api_key or os.getenv("OPENAI_API_KEY")

        # Initialize `model_id` and `messages`
        self.model_id = model_id
        self.messages: Messages = []

        # Update config with user-provided config
        self.inference_config = OpenAIConfig()
        self.inference_config.update(inference_config)

        logger.debug("inference_config=<%s> | initialized", self.inference_config)

        # Lazy initialization for clients
        self._client: OpenAI | None = None
        self._async_client: AsyncOpenAI | None = None

    @property
    def client(self) -> OpenAI:
        if self._client is None:
            self._client = OpenAI(
                base_url=self.base_url,
                api_key=self.api_key,
            )
            logger.info("OpenAI client initialized")
        return self._client

    @property
    def async_client(self) -> AsyncOpenAI:
        if self._async_client is None:
            self._async_client = AsyncOpenAI(
                base_url=self.base_url,
                api_key=self.api_key,
            )
            logger.info("OpenAI ASYNC client initialized")
        return self._async_client

    def update_config(self, **inference_config: Unpack[OpenAIConfig]) -> None:
        """Update the OpenAI Model configuration with the provided arguments.

        Args:
            **inference_config: Configuration overrides.
        """
        self.inference_config.update(inference_config)

    def get_config(self) -> OpenAIConfig:
        """Get the current OpenAI Model configuration.

        Returns:
            The OpenAI model configuration.
        """
        return self.inference_config

    def add_message(self, role: OpenAIRole, content: str | Content) -> None:
        """Add a message to the conversation.

        Args:
            role: The role of the message ("user", "developer", "assistant", "tool")
            content: The content of the message (string or list of content blocks)
        """
        # Convert string content to proper OpenAI format
        if isinstance(content, str):
            if role in ("user", "developer"):
                content_blocks = [{"type": "input_text", "text": content}]
            else:  # if role is "assistant" or "tool"
                content_blocks = [{"type": "output_text", "text": content}]
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

    def format_request(
        self,
        messages: Messages | None = None,
    ) -> dict[str, Any]:
        """Build OpenAI Response API request arguments.

        Returns:
            A dictionary of arguments for the OpenAI Response API.
        """
        # Use internal messages if not provided
        if messages is None:
            messages = self.messages

        # Handle reasoning models (o-series and gpt-5 models) temperature override
        # Default temperature is 1, see: https://platform.openai.com/docs/api-reference/responses/create#responses_create-temperature
        temperature = self.inference_config.get("temperature", 1.0)
        if self.model_id in (OPENAI_O_MODEL_LIST + OPENAI_GPT5_MODEL_LIST) and temperature != 1.0:
            print(f"⚠️  Warning: {self.model_id} only supports temperature=1.0, setting temperature to 1.0")
            temperature = 1.0

        # Handle o-series model reasoning effort override
        # "minimal" only works for gpt-5 models, see: https://cookbook.openai.com/examples/gpt-5/gpt-5_new_params_and_tools
        reasoning_effort = self.inference_config.get("reasoning_effort", "medium")
        if self.model_id in OPENAI_O_MODEL_LIST and reasoning_effort == "minimal":
            print(f"⚠️  Warning: {self.model_id} does support reasoning_effort='minimal', setting reasoning_effort to 'low'")
            reasoning_effort = "low"

        # Build reasoning arguments for reasoning models (o-series and gpt-5 models)
        reasoning_dict = {
            key: value
            for key, value in [
                ("effort", self.inference_config.get("reasoning_effort")),
                ("summary", self.inference_config.get("reasoning_summary")),
            ]
            if value is not None and self.model_id in (OPENAI_O_MODEL_LIST + OPENAI_GPT5_MODEL_LIST)
        }
        if reasoning_dict:
            print(f"🧠 Reasoning arguments: {reasoning_dict}")

        # Build text arguments
        text_dict: dict[str, Any] = {}
        if self.inference_config.get("response_format"):
            text_dict["format"] = self.inference_config.get("response_format")
        if self.inference_config.get("verbosity") and self.model_id in OPENAI_GPT5_MODEL_LIST:
            text_dict["verbosity"] = self.inference_config.get("verbosity")
        if text_dict:
            print(f"📣 Text arguments: {text_dict}")

        return {
            "model": self.model_id,
            "input": messages,
            "temperature": temperature,
            **{
                key: value
                for key, value in [
                    ("max_output_tokens", self.inference_config.get("max_output_tokens")),
                    ("top_p", self.inference_config.get("top_p")),
                    ("frequency_penalty", self.inference_config.get("frequency_penalty")),
                    ("presence_penalty", self.inference_config.get("presence_penalty")),
                    ("logit_bias", self.inference_config.get("logit_bias")),
                    ("logprobs", self.inference_config.get("logprobs")),
                    ("top_logprobs", self.inference_config.get("top_logprobs")),
                    ("n", self.inference_config.get("n")),
                    ("stop", self.inference_config.get("stop")),
                    ("prompt_cache_key", self.inference_config.get("prompt_cache_key")),
                    ("stream", self.inference_config.get("stream")),
                    ("stream_options", self.inference_config.get("stream_options")),
                    ("store", self.inference_config.get("store")),
                    ("metadata", self.inference_config.get("metadata")),
                    ("user", self.inference_config.get("user")),
                    ("previous_response_id", self.inference_config.get("previous_response_id")),
                    ("tools", self.inference_config.get("tools")),
                    ("tool_choice", self.inference_config.get("tool_choice")),
                    ("parallel_tool_calls", self.inference_config.get("parallel_tool_calls")),
                ]
                if value is not None
            },
            **({"reasoning": reasoning_dict} if reasoning_dict else {}),
            **({"text": text_dict} if text_dict else {}),
        }

    def extract_response(self, response: Any) -> tuple[str, dict, list[str]]:
        # Extract response text
        response_text = ""
        if response.output and len(response.output) > 0:
            message_output = None
            for item in response.output:
                if hasattr(item, "type") and item.type == "message":
                    message_output = item
                    break
            if message_output and hasattr(message_output, "content") and isinstance(message_output.content, list):
                for content_item in message_output.content:
                    if hasattr(content_item, "type") and content_item.type == "output_text":
                        if hasattr(content_item, "text"):
                            response_text = content_item.text
                            break

        # Extract token usage
        usage = {}
        if hasattr(response, "usage") and response.usage:
            try:
                # Use exclude_none=True to handle fields with None values
                usage = response.usage.model_dump(exclude_none=True)
            except (AttributeError, TypeError, ValueError) as e:
                # Fallback: try to convert to dict if model_dump fails
                logger.warning("model_dump failed for usage: %s, attempting fallback", e)
                try:
                    if hasattr(response.usage, "__dict__"):
                        usage = {k: v for k, v in response.usage.__dict__.items() if v is not None}
                    else:
                        usage = dict(response.usage) if response.usage else {}
                except Exception as fallback_e:
                    logger.error("Both model_dump and fallback failed: %s", fallback_e)
                    usage = {"error": "Failed to extract usage information"}

        # Extract reasoning summary
        # https://cookbook.openai.com/examples/responses_api/reasoning_items#reasoning-summaries
        reasoning_summary_list: list[str] = []
        for item in response.output:
            if getattr(item, "type", None) == "reasoning" and getattr(item, "summary", None):
                # Get all summary blocks
                for summary_block in item.summary:
                    if hasattr(summary_block, "text"):
                        reasoning_summary_list.append(summary_block.text)

        return response_text, usage, reasoning_summary_list

    # Use the latest OpenAI Response API
    # https://platform.openai.com/docs/api-reference/responses
    # Comparasion with the old Chat Completion API
    # https://platform.openai.com/docs/guides/responses-vs-chat-completions
    def get_response(
        self,
        messages: Messages | None = None,
    ) -> tuple[str, dict, list[str], Any]:
        # Retry until success
        while True:
            response = None  # Initialize response to avoid UnboundLocalError
            try:
                request = self.format_request(messages)
                logger.debug("request=<%s> | making response creation call", request)

                response = self.client.responses.create(**request)
                logger.debug("response=<%s> | received", response)

                response_text, usage, reasoning_summary_list = self.extract_response(response)
                if not response_text:
                    print("⚠️  Warning: response_text is empty, retrying...")
                    continue

                return response_text, usage, reasoning_summary_list, response

            # Handle OpenAI API errors first
            except OpenAIError as e:
                logger.error("OpenAIError during response creation call: %s", e)
                print(f"⚠️  OpenAIError occurred: {e}, retrying...")
                continue

            # Handle all other errors
            except Exception as e:
                logger.error("Unexpected error during response creation call: %s", e)
                print(f"⚠️  Unexpected error occurred: {e}, got the response: {response}")
                print("Retrying...")
                continue

    async def get_response_async(
        self,
        messages: Messages | None = None,
    ) -> tuple[str, dict, list[str], Any]:
        # Retry until success
        while True:
            response = None  # Initialize response to avoid UnboundLocalError
            try:
                request = self.format_request(messages)
                logger.debug("request=<%s> | making ASYNC response creation call", request)

                response = await self.async_client.responses.create(**request)
                logger.debug("response=<%s> | received", response)

                response_text, usage, reasoning_summary_list = self.extract_response(response)
                if not response_text:
                    print("⚠️  Warning: response_text is empty, retrying...")
                    continue

                return response_text, usage, reasoning_summary_list, response

            # Handle OpenAI API errors first
            except OpenAIError as e:
                logger.error("OpenAIError during ASYNC response creation call: %s", e)
                print(f"⚠️  OpenAIError occurred: {e}, retrying...")
                continue

            # Handle all other errors
            except Exception as e:
                print(f"⚠️  Unexpected error occurred: {e}, got the response: {response}")
                print("Retrying...")
                continue


# EXAMPLE USAGE:
# python inference_openai.py
async def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base_url", type=str, default="https://api.openai.com/v1")
    parser.add_argument("--model_id", type=str, default=OPENAI_GPT_MODEL_LIST[0])
    parser.add_argument("--max_completion_tokens", type=int, default=1024)
    parser.add_argument("--temperature", type=float, default=0.1)
    args = parser.parse_args()

    # Create OpenAIModel instance
    openai_model = OpenAIModel(
        base_url=args.base_url,
        model_id=args.model_id,
        max_output_tokens=args.max_completion_tokens,
        temperature=args.temperature,
        prompt_cache_key="cache_key_1",
    )

    print("========================== Client ==========================")
    print(f"Base URL: {openai_model.client.base_url}")
    print(f"Max Retries: {openai_model.client.max_retries}")
    print(f"Timeout: {openai_model.client.timeout}")
    print("========================== Model ==========================")
    print(f"Model ID: {openai_model.model_id}")
    print(f"Model Config: {openai_model.get_config()}")

    # Add a simple list of messages
    # For prompt caching, see: https://platform.openai.com/docs/guides/prompt-caching
    openai_model.add_message(
        "developer",
        (
            "Please answer all questions in detail. "
            "Prompt Caching is enabled for all recent models, gpt-4o and newer. "
            "A minimum of 1024 tokens is required for prompt caching. "
            "This is a " + "very " * 1024 + "long system prompt to test prompt caching."
        ),
    )
    openai_model.add_message(
        "user", "Which model and version are you? When are you created? When is your knowledge cut-off date? What is the current date?"
    )

    # Test sync client
    print("========================== Sync Test ==========================")
    response_text, usage, reasoning_summary_list, _ = openai_model.get_response()
    print("-------------------------- Messages --------------------------")
    pprint(openai_model.messages)
    print("-------------------------- Response --------------------------")
    print(response_text)
    print("-------------------------- Usage --------------------------")
    print(usage)
    print("-------------------------- Reasoning Summary --------------------------")
    print(reasoning_summary_list)
    print("========================== Sync End ==========================")

    # Test async client
    print("========================== Async Test ==========================")
    response_text, usage, reasoning_summary_list, _ = await openai_model.get_response_async()
    print("-------------------------- Async Messages --------------------------")
    pprint(openai_model.messages)
    print("-------------------------- Response --------------------------")
    print(response_text)
    print("-------------------------- Usage --------------------------")
    print(usage)
    print("-------------------------- Reasoning Summary --------------------------")
    print(reasoning_summary_list)
    print("========================== Async End ==========================")


if __name__ == "__main__":
    asyncio.run(main())
