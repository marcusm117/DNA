 
# License: Apache 2.0


# Standard Library Modules
import argparse
import json
import math
import os
from typing import TypeAlias, Any

# External Modules
from transformers import AutoTokenizer, AutoConfig
from vllm import LLM, SamplingParams


# Type Aliases
Message: TypeAlias = dict[str, Any]
Messages: TypeAlias = list[Message]


# Set environment variables
os.environ["VLLM_WORKER_MULTIPROC_METHOD"] = "spawn"


def prepare_input_str(input_messages: Messages, model_path: str, use_chat_template: bool) -> str:
    tokenizer = AutoTokenizer.from_pretrained(model_path, use_fast=True)

    # if `use_chat_template` is set True and the model has a chat template, apply it
    if use_chat_template and tokenizer.chat_template:
        print(f"Applying chat template {tokenizer.chat_template} ...")
        result = tokenizer.apply_chat_template(input_messages, tokenize=False, add_generation_prompt=True)
        return str(result)
    # if `use_chat_template` is set True and no template found, concatenate all content with their roles as the prompt
    if use_chat_template and not tokenizer.chat_template:
        print("WARNING: No chat template found. Concatenating all content with their roles as the prompt.")
        flattened_messages = "\n\n".join([f"## {message['role'].upper()}\n\n{message['content']}" for message in input_messages])
        return flattened_messages
    # otherwise, use the last content from ther role "user" as the prompt
    assert input_messages[-1]["role"] == "user", "The last message in the conversation should be from the role 'user'."
    return str(input_messages[-1]["content"])


def prepare_input_str_batch(input_messages_list: list[Messages], model_path: str, use_chat_template: bool) -> list[str]:
    input_str_list = []
    for messages in input_messages_list:
        input_str = prepare_input_str(messages, model_path, use_chat_template)
        input_str_list.append(input_str)

    return input_str_list


def get_vllm_chat_response(
    conv_history: Messages,
    user_input: str,
    model_path: str,
    vllm_args: argparse.Namespace,
    inference_args: argparse.Namespace,
    output_path: str | None = None,
) -> str:
    # construct the input messages
    messages = conv_history.copy()
    if user_input:
        user_message: Message = {"role": "user", "content": user_input}
        messages.append(user_message)
    # prepare the input string
    input_str = prepare_input_str(messages, model_path, use_chat_template=True)

    # get the number of attention heads from the model config
    config = AutoConfig.from_pretrained(model_path, trust_remote_code=vllm_args.trust_remote_code)
    num_attention_heads = config.num_attention_heads
    # set the tensor parallel size to be gcd(num_attention_heads, num_available_gpus)
    tensor_parallel_size = math.gcd(num_attention_heads, len(os.environ["CUDA_VISIBLE_DEVICES"].split(",")))
    print("================================================================")
    print(f"tensor_parallel_size: {tensor_parallel_size}")
    print("================================================================")

    # if temperature is not 0, or top_p is not 1.0, change top_k to -1
    if inference_args.temperature != 0 or inference_args.top_p != 1.0:
        print("================================================================")
        print("WARNING: temperature is not 0.0 or top_p is not 1.0, changing top_k to -1.")
        print("================================================================")
        inference_args.top_k = -1

    # set the sampling parameters
    sampling_params = SamplingParams(
        top_k=inference_args.top_k,  # default is -1
        top_p=inference_args.top_p,  # default is 1.0
        temperature=inference_args.temperature,  # default is 1.0
        max_tokens=inference_args.max_tokens,  # default is 16
        seed=inference_args.seed,  # default is None
    )

    # load the model
    llm = LLM(
        model=model_path,
        trust_remote_code=vllm_args.trust_remote_code,  # default is False
        dtype=vllm_args.dtype,  # default is "auto"
        enable_prefix_caching=True,  # default is False
        tensor_parallel_size=tensor_parallel_size,  # default is 1
        max_num_seqs=vllm_args.max_num_seqs,  # default is 256
        gpu_memory_utilization=vllm_args.gpu_memory_utilization,  # default is 0.9
        disable_sliding_window=vllm_args.disable_sliding_window,  # default is False
    )

    # run inference for the input
    output_obj = llm.generate(input_str, sampling_params)
    # get the generated text
    response_text: str = output_obj[0].outputs[0].text

    # if `output_path` is provided, save the model responses
    if output_path:
        # create the output directory if it does not exist
        os.makedirs(os.path.dirname(output_path), exist_ok=True)
        # save the model responses to a .json file
        with open(output_path, "w", encoding="utf-8") as writer:
            json.dump({"input_messages": messages, "input_text": input_str, "response_text": response_text}, writer, ensure_ascii=False, indent=4)
            writer.flush()

    return response_text


def batch_inference_vllm(
    input_messages_list: list[Messages],
    input_str_list: list[str],
    model_path: str,
    vllm_args: argparse.Namespace,
    inference_args: argparse.Namespace,
    output_path: str | None = None,
) -> tuple[list[str], list[str]]:
    config = AutoConfig.from_pretrained(model_path, trust_remote_code=vllm_args.trust_remote_code)
    num_attention_heads = config.num_attention_heads
    # set the tensor parallel size to be gcd(num_attention_heads, num_available_gpus)
    tensor_parallel_size = math.gcd(num_attention_heads, len(os.environ["CUDA_VISIBLE_DEVICES"].split(",")))
    print("================================================================")
    print(f"tensor_parallel_size: {tensor_parallel_size}")
    print("================================================================")

    # if temperature is not 0, or top_p is not 1.0, change top_k to -1
    if inference_args.temperature != 0 or inference_args.top_p != 1.0:
        print("================================================================")
        print("WARNING: temperature is not 0.0 or top_p is not 1.0, changing top_k to -1.")
        print("================================================================")
        inference_args.top_k = -1

    # set the sampling parameters
    sampling_params = SamplingParams(
        top_k=inference_args.top_k,  # default is -1
        top_p=inference_args.top_p,  # default is 1.0
        temperature=inference_args.temperature,  # default is 1.0
        max_tokens=inference_args.max_tokens,  # default is 16
        seed=inference_args.seed,  # default is None
    )

    # load the model
    llm = LLM(
        model=model_path,
        trust_remote_code=vllm_args.trust_remote_code,  # default is False
        dtype=vllm_args.dtype,  # default is "auto"
        enable_prefix_caching=True,  # default is False
        tensor_parallel_size=tensor_parallel_size,  # default is 1
        max_num_seqs=vllm_args.max_num_seqs,  # default is 256
        gpu_memory_utilization=vllm_args.gpu_memory_utilization,  # default is 0.9
        disable_sliding_window=vllm_args.disable_sliding_window,  # default is False
    )

    # warmup so that KV cache for the shared prefix is computed
    llm.generate(input_str_list[0], sampling_params)
    # generate with prefix caching
    output_obj_list = llm.generate(input_str_list, sampling_params)
    # get the generated text
    response_text_list = [output_obj.outputs[0].text for output_obj in output_obj_list]

    # if `output_path` is provided, save the model responses
    if output_path:
        # create the output directory if it does not exist
        os.makedirs(os.path.dirname(output_path), exist_ok=True)
        # save the model responses to a .jsonl file
        with open(output_path, "w", encoding="utf-8") as writer:
            for messages, input_text, response_text in zip(input_messages_list, input_str_list, response_text_list):
                writer.write(json.dumps({"input_messages": messages, "input_text": input_text, "response_text": response_text}) + "\n")
                writer.flush()

    return response_text_list, input_str_list


# EXAMPLE USAGE: python inference.py
def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model_path", type=str, default="Qwen/Qwen3-0.6B")
    parser.add_argument("--output_dir", type=str, default="inference_vllm_test")
    parser.add_argument("--cuda_visible_devices", type=str, default="0,1,2,7")
    parser.add_argument("--omp_num_threads", type=int, default=48)
    args = parser.parse_args()

    # set environment variables
    # `tensor_parallel_size` depends on the number of available GPUs
    # cpu-based operation speed depends on the number of OMP threads, better to set it to the number of physical cores
    os.environ["CUDA_VISIBLE_DEVICES"] = args.cuda_visible_devices
    os.environ["OMP_NUM_THREADS"] = str(args.omp_num_threads)

    # prepare test input data
    input_messages: Messages = [
        {"role": "user", "content": "who are you?"},
    ]
    input_messages_list = [input_messages] * 10

    # prepare the input strings
    input_str_list = prepare_input_str_batch(input_messages_list, args.model_path, use_chat_template=True)

    # Ministral-8B-Instruct uses a sliding window of 32k tokens, diasble it to use prefix caching
    disable_sliding_window = "Ministral-8B-Instruct" in args.model_path
    # prepare the vllm arguments
    vllm_args = argparse.Namespace(
        trust_remote_code=True,  # vllm default is False
        dtype="auto",  # vllm default is "auto"
        max_num_seqs=100,  # vllm default is 256
        gpu_memory_utilization=0.95,  # vllm default is 0.9
        disable_sliding_window=disable_sliding_window,  # vllm default is False
    )

    # prepare the inference arguments
    inference_args = argparse.Namespace(
        top_k=1,  # vllm default is -1, set to 1 to ensure greedy decoding
        top_p=1.0,  # vllm default is 1.0
        temperature=0,  # vllm default is 1.0
        max_tokens=2048,  # vllm default is 16
        stop=None,  # vllm default is None
        seed=3407,  # vllm default is None
    )

    # +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # TEST 1: `get_vllm_chat_response` function
    # +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    print("TEST 1: `get_vllm_chat_response` function")
    response_text = get_vllm_chat_response(
        conv_history=[],
        user_input="who are you?",
        model_path=args.model_path,
        vllm_args=vllm_args,
        inference_args=inference_args,
        output_path=os.path.join(args.output_dir, "TEST_1_get_vllm_chat_response.json"),
    )
    print("=================================================================")
    print(response_text)
    print("=================================================================")

    # +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # TEST 2: `batch_inference_vllm` function
    # +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    print("TEST 2: `batch_inference_vllm` function")
    batch_inference_vllm(
        input_messages_list=input_messages_list,
        input_str_list=input_str_list,
        output_path=os.path.join(args.output_dir, "TEST_2_batch_inference_vllm.jsonl"),
        model_path=args.model_path,
        vllm_args=vllm_args,
        inference_args=inference_args,
    )


if __name__ == "__main__":
    main()
