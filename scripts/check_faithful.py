#!/usr/bin/env python3
"""Trampoline: forwards to LeanEuclidPlus/scripts/check_faithful.py with correct cwd.

The Bash tool cwd resets to the repo root on each call. The real check_faithful.py
uses __file__ to locate LeanEuclidPlus/, so it must be run with LeanEuclidPlus as cwd
OR be the __file__. This wrapper uses subprocess.run with cwd=LeanEuclidPlus so the
real script's __file__ resolves correctly.
"""
import sys, os, subprocess

here = os.path.dirname(os.path.abspath(__file__))          # DNA/scripts/
lean = os.path.realpath(os.path.join(here, "..", "LeanEuclidPlus"))
real = os.path.join(lean, "scripts", "check_faithful.py")
result = subprocess.run([sys.executable, real] + sys.argv[1:], cwd=lean)
sys.exit(result.returncode)
