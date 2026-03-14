 
# License: Apache 2.0
# pylint: disable=R0912


# Standard Library Modules
from abc import ABC, abstractmethod
from typing import Any

# Internal Modules
from .type_defs import Messages
from .inference_openai import (
    OpenAIConfig,
    OpenAIModel,
    OPENAI_GPT_MODEL_LIST,
    OPENAI_O_MODEL_LIST,
    OPENAI_GPT5_MODEL_LIST,
)
from .inference_bedrock import (
    BedrockConfig,
    BedrockModel,
    BEDROCK_CLAUDE_MODEL_LIST,
    BEDROCK_CLAUDE_THINKING_MODEL_LIST,
)
from .inference_openrouter import (
    OpenRouterConfig,
    OpenRouterModel,
    OPENROUTER_CLAUDE_MODEL_LIST,
    OPENROUTER_CLAUDE_THINKING_MODEL_LIST,
    OPENROUTER_GEMINI_MODEL_LIST,
    OPENROUTER_GEMINI_THINKING_MODEL_LIST,
    OPENROUTER_QWEN3_MODEL_LIST,
    OPENROUTER_QWEN3_THINKING_MODEL_LIST,
    OPENROUTER_GEMMA3_MODEL_LIST,
    OPENROUTER_GPT_OSS_MODEL_LIST,
    OPENROUTER_DEEPSEEK_MODEL_LIST,
    OPENROUTER_DEEPSEEK_THINKING_MODEL_LIST,
)
from .utils import encode_image


class UnifiedModel(ABC):
    """Unified interface for both OpenAI and Bedrock models."""

    @abstractmethod
    def __init__(self, **kwargs: Any) -> None:
        """Initialize the model with configuration."""

    @property
    @abstractmethod
    def model_id(self) -> str:
        """Get the model ID."""

    @property
    @abstractmethod
    def messages(self) -> Messages:
        """Get the messages."""

    @property
    @abstractmethod
    def client(self) -> Any:
        """Get the client."""

    @property
    @abstractmethod
    def async_client(self) -> Any:
        """Get the async client."""

    @property
    @abstractmethod
    def client_args(self) -> dict[str, Any] | None:
        """Get the client arguments."""

    @property
    @abstractmethod
    def session(self) -> Any:
        """Get the session."""

    @property
    @abstractmethod
    def async_session(self) -> Any:
        """Get the async session."""

    @abstractmethod
    def update_config(self, **kwargs: Any) -> None:
        """Update the model configuration."""

    @abstractmethod
    def get_config(self) -> Any:
        """Get the model configuration."""

    @abstractmethod
    def add_messages(self, messages: Messages) -> None:
        """Add a list of messages to the conversation.

        Args:
            messages: List of message objects to be added to the conversation.
        """

    @abstractmethod
    def get_response(self, client: Any, messages: Messages | None = None) -> tuple[str, dict[str, Any], list[str], Any]:
        """Get response synchronously.

        Args:
            messages: Messages in OpenAI format (with "developer" role and content with "type" fields)

        Returns:
            Tuple of (response_text, usage_dict, reasoning_summary_list, response)

        We still return the complete response object/dict in case the user wants to access other fields.
        """

    @abstractmethod
    async def get_response_async(self, client: Any, messages: Messages | None = None) -> tuple[str, dict[str, Any], list[str], Any]:
        """Get response asynchronously.

        Args:
            messages: Messages in OpenAI format (with "developer" role and content with "type" fields)

        Returns:
            Tuple of (response_text, usage_dict, reasoning_summary_list, response)

        We still return the complete response object/dict in case the user wants to access other fields.
        """


class OpenAIModelAdapter(UnifiedModel):
    """Adapter for OpenAI models to provide unified interface."""

    def __init__(self, **kwargs: Any) -> None:
        self._model = OpenAIModel(**kwargs)

    @property
    def model_id(self) -> str:
        return self._model.model_id

    @property
    def messages(self) -> Messages:
        return self._model.messages

    @property
    def client(self) -> Any:
        return self._model.client

    @property
    def async_client(self) -> Any:
        return self._model.async_client

    @property
    def client_args(self) -> dict[str, Any] | None:
        return None

    @property
    def session(self) -> Any:
        return None

    @property
    def async_session(self) -> Any:
        return None

    def update_config(self, **kwargs: Any) -> None:
        self._model.update_config(**kwargs)

    def get_config(self) -> OpenAIConfig:
        return self._model.get_config()

    def convert_messages(self, messages: Messages | None) -> Messages | None:
        # Validate messages
        if messages is None:
            return None

        # Convert messages to OpenAI format, processing image paths if needed
        openai_messages: Messages = []

        for message in messages:
            role = message["role"]
            content = message["content"]

            # No need to convert role, since it is already OpenAIRole
            # Convert content format
            openai_content = []
            for content_item in content:
                # No need to convert input_text and output_text, since they are already in the OpenAI format
                if content_item.get("type") == "input_text":
                    openai_content.append({"type": "input_text", "text": content_item["text"]})
                elif content_item.get("type") == "output_text":
                    openai_content.append({"type": "output_text", "text": content_item["text"]})
                elif content_item.get("type") == "input_image":
                    # Handle image processing for OpenAI
                    if "image_path" in content_item:
                        # Process image path to base64 data URL
                        image_path = content_item["image_path"]
                        image_format = content_item.get("image_format")
                        encoded_string = encode_image(image_path)
                        openai_content.append({"type": "input_image", "image_url": f"data:image/{image_format};base64,{encoded_string}"})
                    # Already processed, use as is
                    elif "image_url" in content_item:
                        openai_content.append(content_item)
                    else:
                        raise ValueError(f"Invalid image content: {content_item}")
                else:
                    raise ValueError(f"Unsupported content type: {content_item.get('type')} for content: {content_item}")

            # Only add message if it has content
            if openai_content:
                openai_messages.append({"role": role, "content": openai_content})

        # If messages is empty, return None
        if not openai_messages:
            return None
        return openai_messages

    def add_messages(self, messages: Messages) -> None:
        # Convert messages to OpenAI format first
        openai_messages = self.convert_messages(messages)
        if openai_messages is not None:
            self._model.add_messages(openai_messages)

    def get_response(self, client: Any, messages: Messages | None = None) -> tuple[str, dict[str, Any], list[str], Any]:
        # Convert messages to OpenAI format first
        openai_messages = self.convert_messages(messages)
        # No need to create client, will use _model.client
        return self._model.get_response(openai_messages)

    async def get_response_async(self, client: Any, messages: Messages | None = None) -> tuple[str, dict[str, Any], list[str], Any]:
        # Convert messages to OpenAI format first
        openai_messages = self.convert_messages(messages)
        # No need to create client, will use _model.async_client
        return await self._model.get_response_async(openai_messages)


class BedrockModelAdapter(UnifiedModel):
    """Adapter for Bedrock models to provide unified interface."""

    def __init__(self, **kwargs: Any) -> None:
        self._model = BedrockModel(**kwargs)

    @property
    def model_id(self) -> str:
        return self._model.model_id

    @property
    def messages(self) -> Messages:
        return self._model.messages

    @property
    def client(self) -> Any:
        return None

    @property
    def async_client(self) -> Any:
        return None

    @property
    def client_args(self) -> dict[str, Any] | None:
        return self._model.client_args

    @property
    def session(self) -> Any:
        return self._model.session

    @property
    def async_session(self) -> Any:
        return self._model.async_session

    def update_config(self, **kwargs: Any) -> None:
        self._model.update_config(**kwargs)

    def get_config(self) -> BedrockConfig:
        return self._model.get_config()

    def convert_messages(self, messages: Messages | None) -> Messages | None:
        # Validate messages
        if messages is None:
            return None

        # Convert OpenAI format to Bedrock format
        bedrock_messages: Messages = []
        system_prompt_parts = []

        for message in messages:
            role = message["role"]
            content = message["content"]

            # Handle system content (developer role) - extract for system prompt
            if role == "developer":
                for content_item in content:
                    if content_item.get("type") == "input_text":
                        system_prompt_parts.append(content_item["text"])
                continue
            if role not in ["user", "assistant"]:
                raise ValueError(f"Unsupported role: {role}")

            # Convert content format
            bedrock_content = []
            for content_item in content:
                if content_item.get("type") == "input_text":
                    bedrock_content.append({"text": content_item["text"]})
                elif content_item.get("type") == "output_text":
                    bedrock_content.append({"text": content_item["text"]})
                elif content_item.get("type") == "input_image":
                    # Handle image processing for Bedrock
                    if "image_path" in content_item:
                        # Read image file directly as raw bytes
                        image_path = content_item["image_path"]
                        image_format = content_item.get("image_format", "png")  # Default to png
                        with open(image_path, "rb") as image_file:
                            raw_bytes = image_file.read()
                        bedrock_content.append({"image": {"format": image_format, "source": {"bytes": raw_bytes}}})
                    else:
                        raise ValueError(f"Invalid image content: {content_item}")
                else:
                    raise ValueError(f"Unsupported content type: {content_item.get('type')} for content: {content_item}")

            # Only add message if it has content
            if bedrock_content:
                bedrock_messages.append({"role": role, "content": bedrock_content})

        # Set system prompt if we extracted any
        if system_prompt_parts:
            self._model.system_prompt = "\n".join(system_prompt_parts)

        # If messages is empty, return None
        if not bedrock_messages:
            return None
        return bedrock_messages

    def add_messages(self, messages: Messages) -> None:
        # Convert messages to Bedrock format first
        converted_messages = self.convert_messages(messages)
        if converted_messages is not None:
            self._model.add_messages(converted_messages)

    def get_response(self, client: Any, messages: Messages | None = None) -> tuple[str, dict[str, Any], list[str], Any]:
        # Convert messages to Bedrock format first
        bedrock_messages = self.convert_messages(messages)
        # The user is responsible for creating the client using the sync session
        # No need to provide system prompt, since it is already set during `convert_messages`
        return self._model.get_response(client, None, bedrock_messages)

    async def get_response_async(self, client: Any, messages: Messages | None = None) -> tuple[str, dict[str, Any], list[str], Any]:
        # Convert messages to Bedrock format first
        bedrock_messages = self.convert_messages(messages)
        # The user is responsible for creating the async client using the async session
        # No need to provide system prompt, since it is already set during `convert_messages`
        return await self._model.get_response_async(client, None, bedrock_messages)


class OpenRouterModelAdapter(UnifiedModel):
    """Adapter for OpenRouter models to provide unified interface."""

    def __init__(self, **kwargs: Any) -> None:
        self._model = OpenRouterModel(**kwargs)

    @property
    def model_id(self) -> str:
        return self._model.model_id

    @property
    def messages(self) -> Messages:
        return self._model.messages

    @property
    def client(self) -> Any:
        return self._model.client

    @property
    def async_client(self) -> Any:
        return self._model.async_client

    @property
    def client_args(self) -> dict[str, Any] | None:
        return None

    @property
    def session(self) -> Any:
        return None

    @property
    def async_session(self) -> Any:
        return None

    def update_config(self, **kwargs: Any) -> None:
        self._model.update_config(**kwargs)

    def get_config(self) -> OpenRouterConfig:
        return self._model.get_config()

    def convert_messages(self, messages: Messages | None) -> Messages | None:
        # Validate messages
        if messages is None:
            return None

        # Convert messages to OpenAI Response API format, processing image paths if needed
        openrouter_messages: Messages = []

        for message in messages:
            role = message["role"]
            content = message["content"]

            #  Convert the "developer" role to "system" role
            if role == "developer":
                role = "system"
            if role not in ["system", "user", "assistant", "tool"]:
                raise ValueError(f"Unsupported role: {role}")

            # Convert content format
            openrouter_content = []
            for content_item in content:
                # Convert type to "text"
                if content_item.get("type") == "input_text":
                    openrouter_content.append({"type": "text", "text": content_item["text"]})
                elif content_item.get("type") == "output_text":
                    openrouter_content.append({"type": "text", "text": content_item["text"]})
                elif content_item.get("type") == "input_image":
                    # Handle image processing for OpenRouter (same as OpenAI)
                    if "image_path" in content_item:
                        # Process image path to base64 data URL
                        image_path = content_item["image_path"]
                        image_format = content_item.get("image_format")
                        encoded_string = encode_image(image_path)
                        openrouter_content.append({"type": "image_url", "image_url": {"url": f"data:image/{image_format};base64,{encoded_string}"}})
                    else:
                        raise ValueError(f"Invalid image content: {content_item}")
                else:
                    raise ValueError(f"Unsupported content type: {content_item.get('type')} for content: {content_item}")

            # Only add message if it has content
            if openrouter_content:
                openrouter_messages.append({"role": role, "content": openrouter_content})

        # If messages is empty, return None
        if not openrouter_messages:
            return None
        return openrouter_messages

    def add_messages(self, messages: Messages) -> None:
        # Convert messages to OpenRouter format first
        openrouter_messages = self.convert_messages(messages)
        if openrouter_messages is not None:
            self._model.add_messages(openrouter_messages)

    def get_response(self, client: Any, messages: Messages | None = None) -> tuple[str, dict[str, Any], list[str], Any]:
        # Convert messages to OpenRouter format first
        openrouter_messages = self.convert_messages(messages)
        # No need to create client, will use _model.client
        return self._model.get_response(openrouter_messages)

    async def get_response_async(self, client: Any, messages: Messages | None = None) -> tuple[str, dict[str, Any], list[str], Any]:
        # Convert messages to OpenRouter format first
        openrouter_messages = self.convert_messages(messages)
        # No need to create client, will use _model.async_client
        return await self._model.get_response_async(openrouter_messages)


def create_unified_model(model_id: str, **kwargs: Any) -> UnifiedModel:
    """Factory function to create the appropriate model adapter.

    Args:
        model_id: The model ID to determine which adapter to use
        **kwargs: Additional arguments passed to the model constructor

    Returns:
        A UnifiedModel instance
    """
    # Check for OpenAI models
    if model_id in (OPENAI_GPT_MODEL_LIST + OPENAI_O_MODEL_LIST + OPENAI_GPT5_MODEL_LIST):
        return OpenAIModelAdapter(model_id=model_id, **kwargs)

    # Check for Bedrock models
    if model_id in (BEDROCK_CLAUDE_MODEL_LIST + BEDROCK_CLAUDE_THINKING_MODEL_LIST):
        return BedrockModelAdapter(model_id=model_id, **kwargs)

    # Check for OpenRouter models
    openrouter_models = (
        OPENROUTER_CLAUDE_MODEL_LIST
        + OPENROUTER_CLAUDE_THINKING_MODEL_LIST
        + OPENROUTER_GEMINI_MODEL_LIST
        + OPENROUTER_GEMINI_THINKING_MODEL_LIST
        + OPENROUTER_QWEN3_MODEL_LIST
        + OPENROUTER_QWEN3_THINKING_MODEL_LIST
        + OPENROUTER_GEMMA3_MODEL_LIST
        + OPENROUTER_GPT_OSS_MODEL_LIST
        + OPENROUTER_DEEPSEEK_MODEL_LIST
        + OPENROUTER_DEEPSEEK_THINKING_MODEL_LIST
    )
    if model_id in openrouter_models:
        return OpenRouterModelAdapter(model_id=model_id, **kwargs)

    # For any other model ID, assume it's an OpenRouter model (any OpenAI chat completion compatible model)
    return OpenRouterModelAdapter(model_id=model_id, **kwargs)
