# list of reasoning modes
reasoning_list=(
    "text-only"
    "multi-modal"
)

# list of categories to evaluate on
category_list=(
    "Parallel"
    "Triangle"
    "Quadrilateral"
    "Congruent"
    "Similarity"
    "Parallel Triangle Quadrilateral Congruent Similarity"
    "Additional"
)

# list of temperatures to evaluate on
tmp_list=(
    0.0
    0.1
    0.2
    0.4
    0.6
    0.8
    1.0
    1.2
)

# list of max query to evaluate on
max_query_list=(
    1
    2
    3
    4
    5
    6
)

# list of example choices to evaluate on
example_choices_list_old=(
    "none"
    "Parallel-1"
    "Triangle-1"
    "Quadrilateral-1"
    "Congruent-1"
    "Similarity-1"
    "Parallel-3"
    "dynamic"
    "Parallel-1 Triangle-1 Quadrilateral-1 Congruent-1 Similarity-1"
)

# list of example choices to evaluate on
example_choices_list=(
    "none"
    "Similarity-1"
    # "dynamic"
)

# list of methods to evaluate on
method_list=(
    "1_direct"
    # "2_self-refine"
    # "3_semi-formalize"
    "4_formalized-structure"
)

# list of proprietary models to evaluate on
model_list_prop=(
    # "gpt-4.1-nano-2025-04-14"
    "gpt-4.1-mini-2025-04-14"
    "gpt-4.1-2025-04-14"
    "anthropic/claude-sonnet-4"
    # "us.anthropic.claude-3-5-haiku-20241022-v1:0"
    # "us.anthropic.claude-3-7-sonnet-20250219-v1:0"
    # "us.anthropic.claude-sonnet-4-20250514-v1:0"
    # "us.anthropic.claude-3-7-sonnet-20250219-v1:0-thinking"
    # "us.anthropic.claude-sonnet-4-20250514-v1:0-thinking"
    # "gpt-5-nano-2025-08-07"
    "gpt-5-mini-2025-08-07"
    "gpt-5-2025-08-07"
    "anthropic/claude-sonnet-4-thinking"
)

# list of open-source models to evaluate on
model_list_open=(
    # "qwen/qwen3-8b"
    "qwen/qwen3-14b"
    "qwen/qwen3-32b"
    # "qwen/qwen3-30b-a3b-instruct-2507"
    "qwen/qwen3-235b-a22b-2507"
    # "qwen/qwen3-8b-thinking"
    "qwen/qwen3-14b-thinking"
    "qwen/qwen3-32b-thinking"
    "qwen/qwen3-235b-a22b-thinking-2507"
)

# list of model for convience
model_list_specialized=(
    "AI-MO/Kimina-Autoformalizer-7B"
    "huawei-ai4math/Mathesis-Autoformalizer-HPO"
    "Goedel-LM/Goedel-Formalizer-V2-8B"
    "Goedel-LM/Goedel-Formalizer-V2-32B"
    "stepfun-ai/StepFun-Formalizer-7B"
    "stepfun-ai/StepFun-Formalizer-32B"
)

# other parameters
EXAMPLE_FORMAT="content"
NUM_RUN=5
NUM_ASYNC_PRED=20
NUM_PROCESS_PRED=100
BATCH_SIZE_EVAL=5
NUM_PROCESS_EVAL=100

# main loop
for tmp in "${tmp_list[@]:2:1}"; do
    for max_query in "${max_query_list[@]:5:1}"; do
        # max retry is (max_query - 1)
        max_retry=$((max_query - 1))

        for reasoning in "${reasoning_list[@]:0:1}"; do

            for example_choice in "${example_choices_list[@]:1:1}"; do
                # remove spaces in example_choice for result_dir_name
                example_choice_stripped=$(echo $example_choice | tr -d ' ')

                # num_examples is 0 if example_choice is "none"
                if [ "$example_choice" == "none" ]; then
                    num_examples=0
                # num_examples is 1 if example_choice is "dynamic"
                elif [ "$example_choice" == "dynamic" ]; then
                    num_examples=1
                # otherwise, count the number of examples by counting patterns like "Parallel-1"
                else
                    num_examples=$(echo "$example_choice" | egrep -o '[A-Za-z]+-[0-9]+' | wc -l)
                fi

                for method in "${method_list[@]:0:2}"; do
                    for model in "${model_list_prop[@]:0:1}"; do

                        for category in "${category_list[@]:5:1}"; do
                            # run autoformalization pipeline
                            python autoformalize_pipeline.py --dataset UniGeo --category $category --reasoning $reasoning --num_query $max_query --num_examples $num_examples --example_choices $example_choice --example_format $EXAMPLE_FORMAT --cot_for_reasoning_models full --method $method --model $model --openai_reasoning_effort medium --num_process $NUM_PROCESS_PRED --num_async $NUM_ASYNC_PRED --enable_caching --temperature $tmp --num_run $NUM_RUN --relations_file Relations_learned --dsl_doc doc_learned.txt --result_dir_name result_dsl-learned
                            # run evaluation
                            python evaluate.py --dataset UniGeo --category $category --reasoning $reasoning --num_examples $num_examples --example_choices $example_choice --method $method --model $model --openai_reasoning_effort medium --num_process $NUM_PROCESS_EVAL --batch_size $BATCH_SIZE_EVAL --num_run $NUM_RUN --ground_relations_file Relations --test_relations_file Relations_learned --result_dir_name result_dsl-learned # result_dsl-barebone result_dsl-learned result_dsl-oracle
                        done
                    done
                done
            done
        done
    done
done