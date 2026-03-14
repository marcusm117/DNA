# License: Apache 2.0
# pylint: disable=R0902


# Standard Library Modules
import asyncio
import logging
import os
import re

# Internal Modules
from .inference_openai import OpenAIModel
from .type_defs import Messages


# Constants for default categories
DEFAULT_CATEGORIES = ["proof", "calculation", "search", "construction", "transformation", "comparison", "binary", "math_word_problem", "other"]

# Default categorization prompt
DEFAULT_CATEGORIZATION_PROMPT = (
    "You are an expert in mathematical problems. Your task is to categorize a problem into one of the following categories:\n\n"
    "1. **proof** - Problems that ask to prove, show, demonstrate, or establish that some claim, statement, proposition, or property is true. "
    "For problems with multiple parts/sub-problems, **as long as one part/sub-problem is a proof**, "
    "the whole problem should be categorized as proof.\n"
    "2. **calculation** - Problems that ask to calculate, count, compute, evaluate, or determine a metric, "
    "a value of an expression, or a specific numerical value (area, volume, angle, length, probability, etc.)\n"
    "3. **search** - Problems that ask to find, describe, or determine a value or mathematical object that satisfy some conditions, "
    "a solution to an equation, a witness of some properties, a counterexample, a max/min value, or a set of such values\n"
    "4. **construction** - Problems that ask to construct, build, draw, or create a geometric structure\n"
    "5. **transformation** - Problems that ask to convert, transform, or simplify "
    "a mathematical expression, equation, inequality, or other mathematical object (e.g. coordinate system, units, etc.)\n"
    "6. **comparison** - Problems that ask to compare, order, rank, or determine relationships between mathematical objects or values\n"
    "7. **binary** - Problems that ask to prove or disprove a statement, determine truth value, "
    "is some statment true, does some mathematical object exist or have certain properties, "
    "find some mathematical object or prove it does not exist, etc.\n"
    "8. **math_word_problem** - Problems that ask to solve a math word problem, "
    "which is a problem that asks to find or solve a value in a real-world context or application\n"
    "9. **other** - Please try your best to fit the problem into the above categories as much as possible, "
    "only use this category when absolutely necessary.\n\n"
    "There might be problems of mixed categories, in which case you should choose the most appropriate category. "
    "For one example, a problem might be asking you to prove an inequality and to determine the equality condition, "
    "in which case you should choose the category of proof since the inequality is the main focus.\n"
    "For another, a problem might be asking you to find, determine, or describe some value with proof, or find and then show it, "
    "in which case you should choose the category of search since the finding is the main focus.\n\n"
    "Similarly, a problem might be asking you to calculate or simplify, and then show it, "
    "in which case you should choose the category of calculation or transformation since the calculation or transformation is the main focus.\n\n"
    "Please respond with ONLY the category name surrounded by triple angle brackets.\n"
    "Example: <<<proof>>> or <<<calculation>>> or <<<search>>> "
    "or <<<construction>>> or <<<transformation>>> or <<<comparison>>> or <<<binary>>> or <<<other>>>\n\n"
    "Problem text:\n\n"
)


class MathProblemClassifier:
    """General classifier for mathematical problems using OpenAI API"""

    def __init__(
        self,
        valid_categories: list[str] | None = None,
        categorization_prompt: str | None = None,
        openai_api_key: str | None = None,
        model_id: str = "gpt-4.1-2025-04-14",
        temperature: float = 0.0,
        use_llm: bool = True,
        num_async: int = 10,
        max_retries: int = 5,
    ):
        # Set defaults if not provided
        self.valid_categories = valid_categories or DEFAULT_CATEGORIES
        self.model_id = model_id
        self.temperature = temperature
        self.max_retries = max_retries

        # Default categorization prompt if not provided
        if categorization_prompt is None:
            self.categorization_prompt = DEFAULT_CATEGORIZATION_PROMPT
        else:
            self.categorization_prompt = categorization_prompt

        # Setup logging - use DEBUG for detailed logs, INFO for cleaner output with progress bars
        log_level = os.environ.get("CLASSIFIER_LOG_LEVEL", "INFO")
        logging.basicConfig(level=getattr(logging, log_level), format="%(asctime)s - %(levelname)s - %(message)s")
        self.logger = logging.getLogger(__name__)
        self.semaphore = asyncio.Semaphore(num_async)  # Limit concurrent requests

        # Initialize OpenAI model if API key is provided
        # Fallback to environment variable if no key provided
        if openai_api_key is None:
            openai_api_key = os.getenv("OPENAI_API_KEY")

        if openai_api_key and use_llm:
            self.openai_model: OpenAIModel | None = OpenAIModel(
                api_key=openai_api_key,
                model_id=model_id,
                temperature=temperature,
                max_output_tokens=128,
            )
        else:
            self.openai_model = None

    async def classify_problem(self, problem_text: str) -> str:
        """Classify a single problem text and return the category"""
        if not self.openai_model:
            raise ValueError("OpenAI model not initialized, please provide an API key")

        # Construct messages
        messages: Messages = [
            {"role": "user", "content": [{"type": "input_text", "text": self.categorization_prompt + problem_text}]},
        ]

        for _ in range(self.max_retries + 1):
            async with self.semaphore:  # Limit concurrent requests
                # Get response from model
                response_text, _, _, _ = await self.openai_model.get_response_async(messages)
                # Add the assistant response to the context
                messages.append({"role": "assistant", "content": [{"type": "output_text", "text": response_text}]})

                # CHECK 1: The response must be surrounded by triple angle brackets
                pattern = r"<<<(.*?)>>>"
                matches = re.findall(pattern, response_text, re.DOTALL)
                if not matches:
                    feedback = (
                        "I couldn't find your category in the expected format. "
                        "Please make sure to provide your category within **triple angle brackets**: <<< category >>>"
                    )
                    messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
                    continue

                # CHECK 2: The response must be a valid category
                model_prediction: str = matches[-1].strip()
                if model_prediction not in self.valid_categories:
                    feedback = f"Invalid category '{model_prediction}'. The category must be one of the following: {self.valid_categories}"
                    messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
                    continue

                return model_prediction

        raise ValueError("All parsing attempts failed, defaulting to 'other'")

    def categorize_problem_placeholder(self, _problem_text: str, index: int) -> str:
        """Placeholder categorization for testing without LLM calls"""
        # Exclude "other" from rotation
        return self.valid_categories[index % (len(self.valid_categories) - 1)]
