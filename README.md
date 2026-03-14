# Divded & Abstract (DNA)

[![License](https://img.shields.io/badge/License-Apache_2.0-green)](https://github.com/marcusm117/DNA/blob/main/LICENSE)

The Divded & Abstract (DNA) Framework for Autoformalization of Mathematical Statements. Official implementation of the ICLR 2026 paper [Divide and Abstract: Autoformalization via Decomposition and Abstraction Learning](openreview.net/forum?id=NjgaeXNit3).

DNA is a 2-phase framework:

1. In Phase I, Abstraction Learning, the framework first extracts common mathematical concepts from the entire informal corpus and formalizes them as reusable abstractions.
2. In Phase II, Decomposition Learning, conditioned on the learned library of abstractions, DNA decomposes each informal statement in the corpus into a structured collection of informal clauses, translates each clause into its formal correspondents, composes the formal clauses back together, and refines the final formalization given feedback from a symbolic validator.

The entire framework requires zero training and thus scales to any formal language, particularly low-resource Domain-Specific Languages (DSL).

<img src="./images/main.png" alt="image" width="800" height="auto">

## Installation

Create and Activate a Conda Environment.

``` bash
conda create -n dna python=3.11
conda activate dna
```

Install from Source with all Dependencies.

``` bash
git clone https://github.com/anonymousauthor567/DivdedAndAbstract.git
cd DivdedAndAbstract
make develop
```

## Usage

To run the Abstraciton Learning phase, please refer to the [README.md](Abstraction_Learning/README.md) file in the Abstraction_Learning folder.

To run the Decomposition Learning phase (without the learned abstraction, with learned abstraction, with oracle abstraction)

- For the LeanEuclidPlus benchmark, please refer to the [README.md](LeanEuclidPlus/README.md) file in the LeanEuclidPlus folder.

- For the ProofNet-Hard benchmark, please refer to the [README.md](ProofNet-Hard/README.md) file in the ProofNet-Hard folder.



## Linting & Testing

We use a `Makefile` as a command registry:

- `make fix`: autoformat the code with `black`
- `make lint`: perform static analysis of the code with `black`, `flake8`, and `pylint`
- `make type`: run type checking using `mypy`
- `make test`: run automated tests using `pytest`
- `make check`: check assets for packaging

Make sure that `make lint`, `make test`, `make type`, and `make check` all pass locally before submitting a Pull Request.
