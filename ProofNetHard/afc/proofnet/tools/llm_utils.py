from __future__ import annotations

import asyncio
from typing import Optional, Dict

from easydict import EasyDict
from openai import AsyncOpenAI


def build_async_text_generator(
    *,
    api_url: Optional[str],
    model: str,
    token: Optional[str],
    retries: int = 5,
):
    client = AsyncOpenAI(api_key=token, base_url=api_url)

    async def async_generate_single_api(input_prompt: str, sampling_params: Dict):
        for _ in range(max(1, retries)):
            try:
                result = await client.chat.completions.create(
                    model=model,
                    messages=[
                        {"role": "system", "content": "You are a helpful assistant"},
                        {"role": "user", "content": input_prompt},
                    ],
                    **sampling_params,
                )
                return (result.choices[0].message.content or "") if result and result.choices else ""
            except Exception:
                await asyncio.sleep(5)
        return ""

    async def async_generate(input_prompt: str, url: Optional[str], sampling_params: Dict):
        n = int(sampling_params.get("n", 1) or 1)
        sampling_params = dict(sampling_params)
        sampling_params["n"] = 1
        outputs = await asyncio.gather(
            *[async_generate_single_api(input_prompt=input_prompt, sampling_params=sampling_params) for _ in range(n)]
        )
        return EasyDict(outputs=[EasyDict(text=o) for o in outputs])

    return async_generate

