# License: Apache 2.0


# Standard Library Modules
from typing import Any, Literal, TypeAlias

# External Modules
from typing_extensions import TypedDict


# OpenAI: "developer" is the new system role for OpenAI models
# https://model-spec.openai.com/
OpenAIRole: TypeAlias = Literal["developer", "user", "assistant", "tool"]

# Bedrock: system prompt is handled separately for Bedrock models
# https://boto3.amazonaws.com/v1/documentation/api/latest/reference/services/bedrock-runtime/client/converse.html
BedrockRole: TypeAlias = Literal["user", "assistant"]

# OpenRouter: tools are handled separately
# https://openrouter.ai/docs/api-reference/overview
OpenRouterRole: TypeAlias = Literal["system", "user", "assistant", "tool"]

# vLLM: uses standard chat template roles
# https://docs.vllm.ai/en/latest/
VLLMRole: TypeAlias = Literal["system", "user", "assistant"]


Content: TypeAlias = list[dict[str, Any]]


class Message(TypedDict):
    role: BedrockRole | OpenAIRole | OpenRouterRole | VLLMRole
    content: Content


Messages: TypeAlias = list[Message]
