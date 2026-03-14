#!/bin/bash
# This script was designed to run on GitHub Codespaces.

# Install elan.
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | bash -s -- -y
source $HOME/.elan/env

# Build and Install CVC5.
# cvc5 version 1.2.2-dev.159.82ff0f2f3
git clone https://github.com/cvc5/cvc5.git && cd cvc5 && git checkout 82ff0f2f3
./configure.sh --auto-download
cd build && make -j8 && sudo make install
cd ../..

# Build and Install Z3.
# z3 version 4.14.2
git clone https://github.com/Z3Prover/z3.git && cd z3 && git checkout 2e2a2e28df7cc6c1d2dc9401e3ebf873fb3148f5
python3 scripts/mk_make.py
cd build && make -j8 && sudo make install
cd ../..

pip install smt-portfolio

# Build the Lean project.
lake script run check
lake exe cache get
lake build SystemE E3 UniGeo UniGeo.Relations_oracle UniGeo.Relations_learned
# Optional.
lake build Book Examples

# All lake builds are successful on:
# 1. Amazon Linux 2023 kernel-6.1 AMI
# 2. Ubuntu Server 22.04 LTS
# 3. Debian GNU/Linux 11