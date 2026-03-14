"""
Top-level package for afc.proofnet

To avoid import-time side effects and warnings when executing submodules
via `python -m afc.proofnet.proofnet_checker`, this package uses lazy
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
    "Simplifier": ("afc.proofnet.tools.simplifier", "Simplifier"),
    "Validator": ("afc.proofnet.proofnet_validator", "Validator"),
    "EquivalenceChecker": ("afc.proofnet.proofnet_checker", "EquivalenceChecker"),
    "EquivalenceResultsAnalyzer": ("afc.proofnet.tools.analysis", "EquivalenceResultsAnalyzer"),
    "EquivalenceResultsManager": ("afc.proofnet.tools.analysis", "EquivalenceResultsManager"),
    "CheckerFast": ("afc.proofnet.fastchecker", "CheckerFast"),
}


def __getattr__(name: str) -> Any:  # PEP 562 lazy import hook
    if name in _LAZY_ATTRS:
        mod_name, attr = _LAZY_ATTRS[name]
        mod = import_module(mod_name)
        obj = getattr(mod, attr)
        globals()[name] = obj
        return obj
    raise AttributeError(f"module 'afc.proofnet' has no attribute {name!r}")
