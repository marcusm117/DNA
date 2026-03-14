#!/usr/bin/env bash
set -euo pipefail

# Install Lean 4 toolchain, Mathlib4, and REPL at pinned commits.
# After success, use the printed paths for:
#   --mathlib_root <PREFIX>/mathlib4
#   --repl_root    <PREFIX>/repl
#
# Pinned versions (from README):
#   Lean 4:        4.7.0-rc2
#   Mathlib 4:     59fdb6b04d7d16825a54483d550d9572ff473abf
#   REPL:          2ab7948163863ee222891653ac98941fe4f20e87
#
# Usage examples:
#   bash install_lean_env.sh                          # default PREFIX="$(pwd)/lean-env"
#   bash install_lean_env.sh --prefix /opt/lean-env   # custom install location
#
# Notes:
# - Requires: git, curl, bash. The script will install elan (Lean toolchain manager) if missing.
# - Building uses Lake; caches are downloaded with `lake exe cache get` when available.

LEANDIST="leanprover/lean4:4.7.0-rc2"
MATHLIB_COMMIT="59fdb6b04d7d16825a54483d550d9572ff473abf"
REPL_COMMIT="2ab7948163863ee222891653ac98941fe4f20e87"
PREFIX="$(pwd)/lean-env"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --prefix)
      PREFIX="$2"; shift 2;;
    -h|--help)
      sed -n '1,80p' "$0"; exit 0;;
    *)
      echo "Unknown arg: $1" >&2; exit 1;;
  esac
done

echo "[+] Using PREFIX=${PREFIX}"
mkdir -p "${PREFIX}"

have_cmd() { command -v "$1" >/dev/null 2>&1; }

ensure_elan() {
  if have_cmd elan && have_cmd lean && have_cmd lake; then
    echo "[+] Found elan/lean/lake"
    return 0
  fi
  echo "[+] Installing elan (Lean toolchain manager)"
  # This will prompt-less install elan into the user profile
  curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y
  # shellcheck source=/dev/null
  if [ -f "$HOME/.elan/env" ]; then
    source "$HOME/.elan/env"
  else
    export PATH="$HOME/.elan/bin:$PATH"
  fi
  if ! have_cmd elan; then
    echo "[-] elan not found on PATH after installation" >&2
    exit 1
  fi
}

pin_toolchain() {
  echo "[+] Installing Lean toolchain ${LEANDIST}"
  elan toolchain install "${LEANDIST}" || true
  elan default "${LEANDIST}" || true
  echo "[+] Lean version: $(lean --version || true)"
}

clone_or_update() {
  local repo_url="$1"; shift
  local dest="$1"; shift
  local commit="$1"; shift
  if [ -d "$dest/.git" ]; then
    echo "[+] Updating repo: $dest"
    git -C "$dest" fetch --all --tags
  else
    echo "[+] Cloning $repo_url -> $dest"
    git clone "$repo_url" "$dest"
  fi
  git -C "$dest" checkout "$commit"
}

build_lake_project() {
  local proj="$1"; shift
  echo "[+] Building with Lake: $proj"
  pushd "$proj" >/dev/null
  # Ensure lake.json deps are resolved, try to get cache when available
  lake update || true
  lake exe cache get || true
  lake build
  popd >/dev/null
}

main() {
  ensure_elan
  pin_toolchain

  # Mathlib4
  MATHLIB_DIR="${PREFIX}/mathlib4"
  clone_or_update https://github.com/leanprover-community/mathlib4.git "$MATHLIB_DIR" "$MATHLIB_COMMIT"
  build_lake_project "$MATHLIB_DIR"

  # REPL
  REPL_DIR="${PREFIX}/repl"
  clone_or_update https://github.com/leanprover-community/repl.git "$REPL_DIR" "$REPL_COMMIT"
  build_lake_project "$REPL_DIR"

  echo
  echo "[✓] Lean environment ready"
  echo "    --mathlib_root: $MATHLIB_DIR"
  echo "    --repl_root:    $REPL_DIR"
  echo
  echo "Run example:"
  echo "  python -m equivalence.beq_normal \\
    --model /path/to/model \\
    --mathlib_root $MATHLIB_DIR \\
    --eval_set proofnet \\
    --working_root ${PREFIX}/output \\
    --dataset_root ./data \\
    --repl_root $REPL_DIR \\
    --try_num 8 --num_concurrency 8 --temperature 0.0"
}

main "$@"

