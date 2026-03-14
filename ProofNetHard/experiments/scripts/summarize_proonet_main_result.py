import sys
from pathlib import Path

# Add repo root to sys.path so we can import experiments.summarize_proonet_main_result
ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from experiments.summarize_proonet_main_result import main  # type: ignore

if __name__ == "__main__":
    main()
