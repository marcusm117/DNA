"""
Top-level package for dna.proofnet

To avoid import-time side effects and warnings when executing submodules
via `python -m dna.proofnet.proofnet_checker`, this package uses lazy
attribute access (PEP 562) instead of importing heavy submodules at import time.
"""

from __future__ import annotations

from importlib import import_module
from typing import Any

__all__ = [
    "Simplifier",
    "Validator",
    "EquivalenceChecker",
    "EquivalenceResultsAnalyzer",
    "EquivalenceResultsManager",
    "CheckerFast",
]


_LAZY_ATTRS = {
    "Simplifier": ("dna.proofnet.tools.simplifier", "Simplifier"),
    "Validator": ("dna.proofnet.proofnet_validator", "Validator"),
    "EquivalenceChecker": ("dna.proofnet.proofnet_checker", "EquivalenceChecker"),
    "EquivalenceResultsAnalyzer": ("dna.proofnet.tools.analysis", "EquivalenceResultsAnalyzer"),
    "EquivalenceResultsManager": ("dna.proofnet.tools.analysis", "EquivalenceResultsManager"),
    "CheckerFast": ("dna.proofnet.fastchecker", "CheckerFast"),
}


def __getattr__(name: str) -> Any:  # PEP 562 lazy import hook
    if name in _LAZY_ATTRS:
        mod_name, attr = _LAZY_ATTRS[name]
        mod = import_module(mod_name)
        obj = getattr(mod, attr)
        globals()[name] = obj
        return obj
    raise AttributeError(f"module 'dna.proofnet' has no attribute {name!r}")
