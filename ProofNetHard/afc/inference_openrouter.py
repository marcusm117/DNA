 
# License: Apache 2.0
# pylint: disable=R0912


# Standard Library Modules
import argparse
import asyncio
import logging
import os
import time
from pprint import pprint
from typing import Any, Literal

# External Modules
from dotenv import load_dotenv
from openai import OpenAI, AsyncOpenAI, OpenAIError
from typing_extensions import TypedDict, Unpack

# Internal Modules
from .type_defs import OpenRouterRole, Content, Messages


# Load environment variables from the .env file
load_dotenv(dotenv_path="../.env")

# Setup logger for this module
logger = logging.getLogger(__name__)


# Constants
# See the doc below for all model ids
# https://openrouter.ai/models
# Claude 4.1, 4 and 3.7 are hybrid models that can switch between reasoning and non-reasoning
# Claude 3.5 are non-reasoning models, see:
# https://docs.anthropic.com/en/docs/build-with-claude/extended-thinking
OPENROUTER_CLAUDE_MODEL_LIST = [
    "anthropic/claude-3.5-haiku",
    "anthropic/claude-3.7-sonnet",
    "anthropic/claude-sonnet-4",
    "anthropic/claude-opus-4",
    "anthropic/claude-opus-4.1",
]
OPENROUTER_CLAUDE_THINKING_MODEL_LIST = [
    "anthropic/claude-3.7-sonnet-thinking",
    "anthropic/claude-sonnet-4-thinking",
    "anthropic/claude-opus-4-thinking",
    "anthropic/claude-opus-4.1-thinking",
]
# Gemini 2.5 Flash is a hybrid model that can switch between reasoning and non-reasoning
# Gemini 2.5 Pro is a reasoning model with minimal reasoning budget of 128 tokens, see:
# https://ai.google.dev/gemini-api/docs/thinking#set-budget
OPENROUTER_GEMINI_MODEL_LIST = [
    "google/gemini-2.5-flash",
    "google/gemini-2.5-pro",
]
OPENROUTER_GEMINI_THINKING_MODEL_LIST = [
    "google/gemini-2.5-flash-thinking",
    "google/gemini-2.5-pro-thinking",
]
# Qwen 3 0.6B, 1.7B, 4B, 8B, 14B, 32B are hybrid models that can switch between reasoning and non-reasoning
# Qwen 3 Thinking 2507 4B, 30B-A3B, 235B-A22B are reasoning models
# Qwen 3 Instruct 2507 4B, 30B-A3B, 235B-A22B are non-reasoning models, see:
# https://qwen.readthedocs.io/en/latest/
# https://huggingface.co/collections/Qwen/qwen3-67dd247413f0e2e4f653967f
OPENROUTER_QWEN3_MODEL_LIST = [
    # "qwen/qwen3-0.6b-04-28",  # no providers
    # "qwen/qwen3-1.7b",  # no providers
    # "qwen/qwen3-4b:free"  # provider has its own system prompt
    "qwen/qwen3-8b",
    "qwen/qwen3-14b",
    "qwen/qwen3-32b",
    "qwen/qwen3-30b-a3b-instruct-2507",  # non-reasoning model
    "qwen/qwen3-235b-a22b-2507",  # non-reasoning model
    "qwen/qwen3-coder",  # non-reasoning model
]
OPENROUTER_QWEN3_THINKING_MODEL_LIST = [
    "qwen/qwen3-8b-thinking",
    "qwen/qwen3-14b-thinking",
    "qwen/qwen3-32b-thinking",
    "qwen/qwen3-235b-a22b-thinking-2507",
]
# Gemma 3 are non-reasoning models, see:
# https://ai.google.dev/gemma/docs/core#sizes
# https://huggingface.co/collections/google/gemma-3-release-67c6c6f89c4f76621268bb6d
OPENROUTER_GEMMA3_MODEL_LIST = [
    # "google/gemma-3-1b-it",  # no providers
    "google/gemma-3-4b-it",
    "google/gemma-3-12b-it",
    "google/gemma-3-27b-it",
]
# gpt-oss are reasoning models, see:
# https://github.com/openai/gpt-oss
# https://huggingface.co/collections/openai/gpt-oss-68911959590a1634ba11c7a4
OPENROUTER_GPT_OSS_MODEL_LIST = [
    "openai/gpt-oss-20b",
    "openai/gpt-oss-120b",
]
# DeepSeek V3.1 is a hybrid model that can switch between reasoning and non-reasoning
# https://huggingface.co/deepseek-ai/DeepSeek-V3.1
# https://openrouter.ai/deepseek/deepseek-chat-v3.1
OPENROUTER_DEEPSEEK_MODEL_LIST = [
    "deepseek/deepseek-chat-v3.1",
]
OPENROUTER_DEEPSEEK_THINKING_MODEL_LIST = [
    "deepseek/deepseek-chat-v3.1-thinking",
]

OPENROUTER_HYBRID_MODEL_SET = set(
    OPENROUTER_CLAUDE_THINKING_MODEL_LIST + OPENROUTER_GEMINI_THINKING_MODEL_LIST + OPENROUTER_DEEPSEEK_THINKING_MODEL_LIST
)


class MaxPriceConfig(TypedDict, total=False):
    """Maximum price configuration for different types of usage.

    USD price per million tokens.
    """

    prompt: float | str
    completion: float | str
    image: float | str
    audio: float | str
    request: float | str


class ProviderRoutingConfig(TypedDict, total=False):
    """Configuration for OpenRouter provider routing.

    Reference: https://openrouter.ai/docs/features/provider-routing
    """

    # List of provider slugs to try in order (e.g. ["anthropic", "openai"])
    order: list[str]
    # Whether to allow backup providers when the primary is unavailable
    allow_fallbacks: bool
    # Only use providers that support all parameters in your request
    require_parameters: bool
    # Control whether to use providers that may store data
    data_collection: Literal["allow", "deny"]
    # List of provider slugs to allow for this request
    only: list[str]
    # List of provider slugs to skip for this request
    ignore: list[str]
    # List of quantization levels to filter by (e.g. ["int4", "int8"])
    quantizations: list[str]
    # Sort providers by price, throughput, or latency
    sort: Literal["price", "throughput", "latency"]
    # The maximum pricing you want to pay for this request
    max_price: MaxPriceConfig


class FunctionDescription(TypedDict, total=False):
    """Function description for tool calling."""

    name: str  # Required
    parameters: dict[str, Any]  # Required - JSON Schema object
    description: str  # Optional


class Tool(TypedDict):
    """Tool definition for function calling."""

    type: Literal["function"]
    function: FunctionDescription


class ToolChoiceFunction(TypedDict):
    """Function specification for tool choice."""

    name: str


class ToolChoiceObject(TypedDict):
    """Specific tool selection object."""

    type: Literal["function"]
    function: ToolChoiceFunction


# Tool choice: "none", "auto", or specific tool selection
ToolChoice = Literal["none", "auto"] | ToolChoiceObject


class OpenRouterConfig(TypedDict, total=False):
    """Configuration for OpenRouter model parameters.

    Reference: https://openrouter.ai/docs/api-reference/overview
    """

    # Core parameters
    temperature: float
    max_tokens: int
    top_k: int
    top_p: float
    min_p: float
    top_a: float

    # Token generation parameters
    frequency_penalty: float
    presence_penalty: float
    repetition_penalty: float
    logit_bias: dict[int, float]
    top_logprobs: int
    stop: str | list[str]
    seed: int

    # Streaming parameters
    stream: bool

    # Tools and function calling
    tools: list[Tool]
    tool_choice: ToolChoice
    parallel_tool_calls: bool

    # Response format
    response_format: dict

    # Reasoning parameters
    # https://openrouter.ai/docs/use-cases/reasoning-tokens
    reasoning_effort: Literal["low", "medium", "high"]
    reasoning_budget: int
    # https://openrouter.ai/docs/use-cases/reasoning-tokens#excluding-reasoning-tokens
    exclude_reasoning_output: bool
    # https://openrouter.ai/docs/use-cases/reasoning-tokens#enable-reasoning-with-default-config
    enable_reasoning: bool

    # Usage parameters
    # https://openrouter.ai/docs/api-reference/chat-completion#request.body.usage
    include_usage: bool

    # OpenRouter-specific parameters
    # see: https://openrouter.ai/docs/transforms
    transforms: list[str]
    # see: https://openrouter.ai/docs/model-routing
    models: list[str]
    route: Literal["fallback"]
    # see: https://openrouter.ai/docs/provider-routing
    provider: ProviderRoutingConfig
    # A stable identifier for your end-users
    user: str

    # Additional parameters
    additional_args: dict[str, Any]


class OpenRouterModel:
    def __init__(
        self,
        *,  # keyword-only arguments
        base_url: str | None = None,
        api_key: str | None = None,
        model_id: str,
        **inference_config: Unpack[OpenRouterConfig],
    ) -> None:
        """Initialize provider instance.

        Args:
            model_id: The OpenRouter model ID (e.g., "anthropic/claude-3.7-sonnet")
            **inference_config: Configuration options for the OpenRouter model.
        """
        # Initialize `base_url` and `api_key`
        self.base_url = base_url or os.getenv("OPENROUTER_BASE_URL") or "https://openrouter.ai/api/v1"
        self.api_key = api_key or os.getenv("OPENROUTER_API_KEY")

        # Initialize `model_id` and `messages`
        self.model_id = model_id
        self.messages: Messages = []

        # Update config with user-provided config
        self.inference_config = OpenRouterConfig()
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
            logger.info("OpenRouter client initialized")
        return self._client

    @property
    def async_client(self) -> AsyncOpenAI:
        if self._async_client is None:
            self._async_client = AsyncOpenAI(
                base_url=self.base_url,
                api_key=self.api_key,
            )
            logger.info("OpenRouter ASYNC client initialized")
        return self._async_client

    def update_config(self, **inference_config: Unpack[OpenRouterConfig]) -> None:
        """Update the OpenRouter Model configuration with the provided arguments.

        Args:
            **inference_config: Configuration overrides.
        """
        self.inference_config.update(inference_config)

    def get_config(self) -> OpenRouterConfig:
        """Get the current OpenRouter Model configuration.

        Returns:
            The OpenRouter model configuration.
        """
        return self.inference_config

    def add_message(self, role: OpenRouterRole, content: str | Content) -> None:
        """Add a message to the conversation.

        Args:
            role: The role of the message ("system", "user", "assistant")
            content: The content of the message (string or list of content blocks)
        """
        # Convert string content to proper OpenAI format
        if isinstance(content, str):
            if role in ("system", "user"):
                content_blocks = [{"type": "text", "text": content}]
            else:  # if role is "tool"
                raise NotImplementedError("Tool messages are not yet implemented!")
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

    def _get_total_content_tokens(self, messages: Messages) -> int:
        """Calculate total token count for all message content"""
        total_tokens = 0

        for message in messages:
            for content_item in message.get("content", []):
                if content_item.get("text"):
                    total_tokens += self._estimate_token_count(content_item["text"])
                # Note: We don't count image tokens as they don't contribute to text caching

        return total_tokens

    def format_request(
        self,
        messages: Messages | None = None,
    ) -> dict[str, Any]:
        """Build OpenRouter Chat Completions API request arguments.

        Returns:
            A dictionary of arguments for the OpenRouter Chat Completions API.
        """
        # Use internal messages if not provided
        if messages is None:
            messages = self.messages

        # For Qwen3 hybrid models with thinking mode, we need to add "/think" to the content of the last message
        if self.model_id in OPENROUTER_QWEN3_THINKING_MODEL_LIST and self.model_id.endswith("-thinking"):
            assert messages and messages[-1]["role"] == "user", f"For {self.model_id}, the last message must be a user message"
            assert messages[-1]["content"][-1]["type"] == "text", f"For {self.model_id}, the last message must be a text message"
            last_message_text = messages[-1]["content"][-1]["text"]
            # If user add "/think" at the end, do nothing
            if last_message_text.endswith("/think"):
                pass
            # If user add "/no_think" at the end, replace it with "/think"
            elif last_message_text.endswith("/no_think"):
                messages[-1]["content"][-1]["text"] = last_message_text.replace("/no_think", "/think")
            # If user didn't add anything at the end, add "/think"
            else:
                messages[-1]["content"][-1]["text"] += " /think"
        # For Qwen3 hybrid models with non-thinking mode, we need to add "/no_think" to the content of the last message
        elif self.model_id in OPENROUTER_QWEN3_MODEL_LIST and (not self.model_id.endswith("-2507")):
            assert messages and messages[-1]["role"] == "user", f"For {self.model_id}, the last message must be a user message"
            assert messages[-1]["content"][-1]["type"] == "text", f"For {self.model_id}, the last message must be a text message"
            last_message_text = messages[-1]["content"][-1]["text"]
            # If user add "/no_think" at the end, do nothing
            if last_message_text.endswith("/no_think"):
                pass
            # If user add "/think" at the end, replace it with "/no_think"
            elif last_message_text.endswith("/think"):
                messages[-1]["content"][-1]["text"] = last_message_text.replace("/think", "/no_think")
            # If user didn't add anything at the end, add "/no_think"
            else:
                messages[-1]["content"][-1]["text"] += " /no_think"

        # Enable reasoning for hybrid models, when "-thinking" attached at the end of the model id
        if self.model_id in OPENROUTER_HYBRID_MODEL_SET:
            if (
                not self.inference_config.get("enable_reasoning")
                and not self.inference_config.get("reasoning_effort")
                and not self.inference_config.get("reasoning_budget")
            ):
                self.inference_config["enable_reasoning"] = True
                logger.warning(
                    f"{self.model_id} is a reasoning model, but reasoning was disabled; "
                    "forcing enable_reasoning=True at medium effort."
                )

        # Build reasoning arguments for reasoning models
        reasoning_dict = {
            key: value
            for key, value in [
                ("effort", self.inference_config.get("reasoning_effort")),
                ("max_tokens", self.inference_config.get("reasoning_budget")),
                ("exclude", self.inference_config.get("exclude_reasoning_output")),
                ("enabled", self.inference_config.get("enable_reasoning")),
            ]
            if value is not None
        }
        if reasoning_dict:
            logger.debug(f"Reasoning arguments: {reasoning_dict}")

        # Build usage arguments
        usage_dict = {
            key: value
            for key, value in [
                ("include", self.inference_config.get("include_usage")),
            ]
            if value is not None
        }
        if usage_dict:
            logger.debug(f"Usage arguments: {usage_dict}")

        # Build extra_body with openrouter-specific and additional args
        extra_body: dict[str, Any] = {}
        # Add provider parameters to extra_body
        if self.inference_config.get("provider"):
            extra_body["provider"] = self.inference_config.get("provider")
        # Add reasoning parameters to extra_body
        if reasoning_dict:
            extra_body["reasoning"] = reasoning_dict
        # Add usage parameters to extra_body
        if usage_dict:
            extra_body["usage"] = usage_dict
        # Add additional arguments to extra_body
        additional_args = self.inference_config.get("additional_args")
        if additional_args:
            extra_body.update(additional_args)

        # Add cache point for Claude models
        # https://openrouter.ai/docs/features/prompt-caching
        if self.model_id in OPENROUTER_CLAUDE_MODEL_LIST + OPENROUTER_CLAUDE_THINKING_MODEL_LIST:
            # Determine minimum tokens required based on model
            min_tokens_required = 2048  # Default for Claude 3.5 Haiku
            if any(model in self.model_id for model in ["opus", "sonnet"]):
                min_tokens_required = 1024

            # Cache the first message, no matther it's systerm or user message
            total_tokens_first_message = self._get_total_content_tokens(messages[:1])
            if total_tokens_first_message > min_tokens_required:
                # Add cache point to the first message
                messages[0]["content"][-1]["cache_control"] = {"type": "ephemeral"}
                logger.info("Added cache point to the first message")
                print(f"Added cache point to the first message for {self.model_id}")
            else:
                logger.info("Skipping cache point addition - insufficient tokens: %d < %d", total_tokens_first_message, min_tokens_required)
                print(
                    f"Skipping cache point addition - insufficient tokens: {total_tokens_first_message} < {min_tokens_required} for {self.model_id}"
                )

            # Find the last user message before the first assistant message
            # If no assistant messages, use the last message
            last_index = len(messages) - 1  # Default to last message
            for i, message in enumerate(messages):
                if message["role"] == "assistant":
                    last_index = i - 1
                    break

            # Calculate total token count of the messages before the first assistant message
            total_tokens_before_llm = self._get_total_content_tokens(messages[: last_index + 1])

            # Only add cache points if we have enough tokens
            if total_tokens_before_llm > min_tokens_required:
                # Add cache point to the last content block in the last user message
                messages[last_index]["content"][-1]["cache_control"] = {"type": "ephemeral"}
                logger.info("Added cache point to the last user message before any assistant message")
                print(f"Added cache point to the last user message before any assistant message for {self.model_id}")
            else:
                logger.info("Skipping cache point addition - insufficient tokens: %d < %d", total_tokens_before_llm, min_tokens_required)
                print(f"Skipping cache point addition - insufficient tokens: {total_tokens_before_llm} < {min_tokens_required} for {self.model_id}")

        # Remove the trailing "-thinking" for hybrid models
        if self.model_id in OPENROUTER_HYBRID_MODEL_SET:
            model_id = self.model_id.replace("-thinking", "")
        elif self.model_id.endswith("-thinking") and self.model_id in OPENROUTER_QWEN3_THINKING_MODEL_LIST:
            model_id = self.model_id.replace("-thinking", "")
        else:
            model_id = self.model_id

        return {
            "model": model_id,
            "messages": messages,
            **{
                key: value
                for key, value in [
                    ("temperature", self.inference_config.get("temperature")),
                    ("max_tokens", self.inference_config.get("max_tokens")),
                    ("top_p", self.inference_config.get("top_p")),
                    ("top_k", self.inference_config.get("top_k")),
                    ("min_p", self.inference_config.get("min_p")),
                    ("top_a", self.inference_config.get("top_a")),
                    ("frequency_penalty", self.inference_config.get("frequency_penalty")),
                    ("presence_penalty", self.inference_config.get("presence_penalty")),
                    ("repetition_penalty", self.inference_config.get("repetition_penalty")),
                    ("logit_bias", self.inference_config.get("logit_bias")),
                    ("top_logprobs", self.inference_config.get("top_logprobs")),
                    ("stop", self.inference_config.get("stop")),
                    ("seed", self.inference_config.get("seed")),
                    ("stream", self.inference_config.get("stream")),
                    ("tools", self.inference_config.get("tools")),
                    ("tool_choice", self.inference_config.get("tool_choice")),
                    ("parallel_tool_calls", self.inference_config.get("parallel_tool_calls")),
                    ("response_format", self.inference_config.get("response_format")),
                    ("transforms", self.inference_config.get("transforms")),
                    ("models", self.inference_config.get("models")),
                    ("route", self.inference_config.get("route")),
                    ("user", self.inference_config.get("user")),
                ]
                if value is not None
            },
            **({"extra_body": extra_body} if extra_body else {}),
        }

    def extract_response(self, response: Any) -> tuple[str, dict, list[str]]:
        # Extract response text from Chat Completions format
        response_text = ""
        if hasattr(response, "choices") and len(response.choices) > 0:
            choice = response.choices[0]
            if hasattr(choice, "message") and hasattr(choice.message, "content"):
                response_text = choice.message.content or ""

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
        reasoning_summary_list: list[str] = []
        if hasattr(response, "choices") and len(response.choices) > 0:
            choice = response.choices[0]
            if hasattr(choice, "message") and hasattr(choice.message, "reasoning"):
                reasoning = choice.message.reasoning
                if reasoning:
                    # Convert reasoning to list of strings format
                    if isinstance(reasoning, str):
                        reasoning_summary_list = [reasoning]
                    elif isinstance(reasoning, list):
                        reasoning_summary_list = [str(item) for item in reasoning]
                    else:
                        reasoning_summary_list = [str(reasoning)]

        return response_text, usage, reasoning_summary_list

    # Use OpenRouter Chat Completions API
    # https://openrouter.ai/docs/api-reference/overview
    def get_response(
        self,
        messages: Messages | None = None,
    ) -> tuple[str, dict, list[str], Any]:
        # Retry with a hard cap to avoid infinite loops on provider JSON glitches
        attempts = 0
        max_attempts = int(self.inference_config.get("max_retries", 10) or 10)
        while attempts < max_attempts:
            response = None  # Initialize response to avoid UnboundLocalError
            try:
                request = self.format_request(messages)
                logger.debug("request=<%s> | making chat completions call", request)

                response = self.client.chat.completions.create(**request)
                logger.debug("response=<%s> | received", response)

                response_text, usage, reasoning_summary_list = self.extract_response(response)
                if not response_text:
                    print("⚠️  Warning: response_text is empty, retrying...")
                    continue

                return response_text, usage, reasoning_summary_list, response

            # Handle OpenAI API errors first
            except OpenAIError as e:
                error_str = str(e)
                logger.error("OpenAIError during chat completions call: %s", error_str)
                print(f"⚠️  OpenAIError occurred: {error_str}, retrying...")
                # Check if it's a rate limit error, and wait 30 seconds if so
                if "temporarily rate-limited upstream" in error_str:
                    wait_time = 30
                    logger.info("Rate limit error detected, waiting %d seconds before retry", wait_time)
                    print(f"🕒 Rate limit error detected, waiting {wait_time} seconds before retry...")
                    time.sleep(wait_time)
                attempts += 1
                continue

            # Handle response parsing errors specifically (from OpenAI client parsing OpenRouter response)
            except ValueError as e:
                error_str = str(e)
                if "Expecting value" in error_str or "JSON" in error_str:
                    logger.error("Response parsing error during chat completions call: %s", error_str)
                    print(f"⚠️  Response parsing error with model {self.model_id}: {error_str}")
                    wait_time = 5
                    logger.info("Response parsing error detected, waiting %d seconds before retry", wait_time)
                    print(f"🕒 Response parsing error detected, waiting {wait_time} seconds before retry...")
                    time.sleep(wait_time)
                attempts += 1
                continue

            # Handle over context length error
            except TypeError as e:
                error_str = str(e)
                response_str = str(response)
                if "has no len()" in error_str and "Please reduce the length of the messages or completion" in response_str:
                    logger.error("Over context length error during chat completions call, returning error message")
                    print("⚠️  Over context length error during chat completions call, returning error message")
                    return response_str, {}, [], response
                attempts += 1
                continue

            # Handle all other errors
            except Exception as e:
                logger.error("Unexpected error during chat completions call: %s", e)
                print(f"⚠️  Unexpected error occurred: {e}, got the response: {response}")
                print("Retrying...")
                attempts += 1
                continue

        # Exceeded max attempts: return a sentinel so callers can record failure and move on
        logger.error("Exceeded max_attempts=%d for chat completion; returning sentinel text", max_attempts)
        print(f"⚠️  Exceeded max retries ({max_attempts}) for {self.model_id}; skipping this request.")
        return "[ERROR] Response parsing failure (max retries exceeded)", {}, [], None

    async def get_response_async(
        self,
        messages: Messages | None = None,
    ) -> tuple[str, dict, list[str], Any]:
        # Retry with a hard cap to avoid infinite loops on provider JSON glitches
        attempts = 0
        max_attempts = int(self.inference_config.get("max_retries", 10) or 10)
        while attempts < max_attempts:
            response = None  # Initialize response to avoid UnboundLocalError
            try:
                request = self.format_request(messages)
                logger.debug("request=<%s> | making ASYNC chat completions call", request)

                response = await self.async_client.chat.completions.create(**request)
                logger.debug("response=<%s> | received", response)

                response_text, usage, reasoning_summary_list = self.extract_response(response)
                if not response_text:
                    print("⚠️  Warning: response_text is empty, retrying...")
                    continue

                return response_text, usage, reasoning_summary_list, response

            # Handle OpenAI API errors first
            except OpenAIError as e:
                error_str = str(e)
                logger.error("OpenAIError during ASYNC chat completions call: %s", error_str)
                print(f"⚠️  OpenAIError occurred: {error_str}, retrying...")
                # Check if it's a rate limit error, and wait 30 seconds if so
                if "temporarily rate-limited upstream" in error_str:
                    wait_time = 30
                    logger.info("Rate limit error detected, waiting %d seconds before retry", wait_time)
                    print(f"🕒 Rate limit error detected, waiting {wait_time} seconds before retry...")
                    await asyncio.sleep(wait_time)
                attempts += 1
                continue

            # Handle response parsing errors specifically (from OpenAI client parsing OpenRouter response)
            except ValueError as e:
                error_str = str(e)
                if "Expecting value" in error_str or "JSON" in error_str:
                    logger.error("Response parsing error during ASYNC chat completions call: %s", error_str)
                    print(f"⚠️  Response parsing error with model {self.model_id}: {error_str}")
                    wait_time = 5
                    logger.info("Response parsing error detected, waiting %d seconds before retry", wait_time)
                    print(f"🕒 Response parsing error detected, waiting {wait_time} seconds before retry...")
                    await asyncio.sleep(wait_time)
                attempts += 1
                continue

            # Handle over context length error
            except TypeError as e:
                error_str = str(e)
                response_str = str(response)
                if "has no len()" in error_str and "Please reduce the length of the messages or completion" in response_str:
                    logger.error("Over context length error during ASYNC chat completions call, returning error message")
                    print("⚠️  Over context length error during ASYNC chat completions call, returning error message")
                    return response_str, {}, [], response
                attempts += 1
                continue

            # Handle all other errors
            except Exception as e:
                logger.error("Unexpected error during ASYNC chat completions call: %s", e)
                print(f"⚠️  Unexpected error occurred: {e}, got the response: {response}")
                print("Retrying...")
                attempts += 1
                continue

        # Exceeded max attempts: return a sentinel so callers can record failure and move on
        logger.error("Exceeded max_attempts=%d for ASYNC chat completion; returning sentinel text", max_attempts)
        print(f"⚠️  Exceeded max retries ({max_attempts}) for {self.model_id}; skipping this request.")
        return "[ERROR] Response parsing failure (max retries exceeded)", {}, [], None


# EXAMPLE USAGE:
# python inference_openrouter.py
async def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base_url", type=str, default="https://openrouter.ai/api/v1")
    parser.add_argument("--model_id", type=str, default=OPENROUTER_QWEN3_MODEL_LIST[1])
    parser.add_argument("--max_completion_tokens", type=int, default=1024)
    parser.add_argument("--temperature", type=float, default=0.1)
    args = parser.parse_args()

    # Create OpenRouterModel instance
    openrouter_model = OpenRouterModel(
        base_url=args.base_url,
        model_id=args.model_id,
        max_tokens=args.max_completion_tokens,
        temperature=args.temperature,
        enable_reasoning=True,
        provider={"only": ["deepinfra/fp8"]},
    )

    print("========================== Client ==========================")
    print(f"Base URL: {openrouter_model.client.base_url}")
    print(f"Max Retries: {openrouter_model.client.max_retries}")
    print(f"Timeout: {openrouter_model.client.timeout}")
    print("========================== Model ==========================")
    print(f"Model ID: {openrouter_model.model_id}")
    print(f"Model Config: {openrouter_model.get_config()}")

    # Add a simple list of messages
    openrouter_model.add_message(
        "system",
        (
            "Please answer all questions in detail. "
            "A minimum of 1024 tokens is required for prompt caching for most models. "
            "This is a " + "very " * 1024 + "long system prompt to test prompt caching."
        ),
    )
    openrouter_model.add_message(
        "user", "Which model and version are you? When are you created? When is your knowledge cut-off date? What is the current date?"
    )

    # Test sync client
    print("========================== Sync Test ==========================")
    response_text, usage, reasoning_summary_list, _ = openrouter_model.get_response()
    print("-------------------------- Messages --------------------------")
    pprint(openrouter_model.messages)
    print("-------------------------- Response --------------------------")
    print(response_text)
    print("-------------------------- Usage --------------------------")
    print(usage)
    print("-------------------------- Reasoning Summary --------------------------")
    print(reasoning_summary_list)
    print("========================== Sync End ==========================")

    # Test async client
    print("========================== Async Test ==========================")
    response_text, usage, reasoning_summary_list, _ = await openrouter_model.get_response_async()
    print("-------------------------- Async Messages --------------------------")
    pprint(openrouter_model.messages)
    print("-------------------------- Response --------------------------")
    print(response_text)
    print("-------------------------- Usage --------------------------")
    print(usage)
    print("-------------------------- Reasoning Summary --------------------------")
    print(reasoning_summary_list)
    print("========================== Async End ==========================")


if __name__ == "__main__":
    asyncio.run(main())
