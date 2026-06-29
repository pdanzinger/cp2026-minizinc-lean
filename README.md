# Repository

This repository contains code and data for the paper **From LLM Suggestions to Lean Proofs: Verified Redundant Constraints for MiniZinc**

## Repository Layout

- `mzn-to-lean/`: C++ translator from supported MiniZinc models with proposed redundant constraints to Lean 4 theorems. This directory includes the `libminizinc` dependency as a git submodule at `mzn-to-lean/libminizinc`.
- `python/`: Python scripts for experiment orchestration, including LLM-based constraint generation, Lean theorem creation, LLM-based theorem proving and performance evaluations.
- `lean_translation_tests/`: MiniZinc-to-Lean translation test cases, expected targets, and generated Lean proofs/results.
- `paper_evaluations/`: Collected evaluation artifacts for the evaluations shown in the paper.

## Prerequisites

The project was developed and used on Linux (Arch Linux / Ubuntu). Other operating systems may or may not work.

To use the full project, the following requirements need to be met:

- `git`
- `cmake` and standard `C++` build tools, supporting `C++20` or above
- `elan` (the Lean toolchain manager; this provides both `lean` and `lake`)
- `python` with `pip`. Python version `3.12.12` is confirmed to work, similar versions likely work as well
- `MiniZinc` installed on the system

## Set-Up

Clone the repository with the `libminizinc` submodule:

```bash
git clone --recurse-submodules <repo-url>
cd minizinc-lean-verifier
# or initialize the submodule later with: git submodule update --init --recursive
```

Download the correct `lean` and `mathlib` versions:

```bash
(cd lean && lake exe cache get)
```

Optionally, create a python venv and activate it:
```bash
python3.12 -m venv .venv
source .venv/bin/activate
```

Install the required `python` packages:
```bash
python -m pip install -r requirements.txt
```

The `cmake` build for the `C++` compiler will be initiated by the python scripts that require it.

## Environment Variables

Environment variables can be used to specify the MiniZinc executable and LLM API keys:

```bash
# MiniZinc (set if not in PATH)
export MINIZINC_EXECUTABLE="/path/to/minizinc"   # default: "minizinc"

# LLM API keys (used by litellm)
export OPENROUTER_API_KEY="sk-or-..."
export ANTHROPIC_API_KEY="sk-ant-..."
export OPENAI_API_KEY="sk-..."
export GEMINI_API_KEY="sk-..."
```

## Viewing outputs for existing files

View the output of an improver iteration:
```bash
python -m python.improver_review_main ./paper_evaluations/oven-scheduling-problem/output/improver_run.json
python -m python.improver_review_main ./paper_evaluations/mspsp/output/improver_run.json
python -m python.improver_review_main ./paper_evaluations/vrplc/output/improver_run.json
```

View the output of the test set evaluations:
```bash
python -m python.minizinc_benchmark_main --output-file ./paper_evaluations/oven-scheduling-problem/output/evaluation.json
python -m python.minizinc_benchmark_main --output-file ./paper_evaluations/mspsp/output/evaluation.json
python -m python.minizinc_benchmark_main --output-file ./paper_evaluations/vrplc/output/evaluation.json
```


## Usage example

The modules `python.improver_main` and `python.minizinc_benchmark_main` are used to run the iterative improvement loop and compare the final models, respectively. Here is a usage example:

```bash
export OPENROUTER_API_KEY="sk-or-..."
python -m python.improver_main \
  --minizinc-model /path/to/original.mzn \
  --minizinc-data-dir /path/to/train_instances/ \
  --output-file /path/to/out_dir/run.json \
  --sample-model "openrouter/openai/gpt-5.2" \
  --sample-reasoning-effort high \
  --sample-batch-size 3 \
  --benchmark-timeout 5 \
  --benchmark-runs-per-instance 1 \
  --total-steps 3 \
  --verifier-waterfall "openrouter/deepseek/deepseek-v3.2:medium:3:3:1" \
  --output-model /path/to/out_dir/final_model.mzn \
  --cumulative
python -m python.minizinc_benchmark_main \
    --minizinc-data-dir /path/to/test_instances/ \
    --minizinc-solver org.chuffed.chuffed \
    --benchmark-timeout 300 \
    --benchmark-runs-per-instance 1 \
    --objective-sense min \
    /path/to/original.mzn \
    /path/to/out_dir/final_model.mzn
```


## Citation

If you use this software artifact, please cite the associated paper:

Philipp Danzinger and Nysret Musliu. From LLM Suggestions to Lean Proofs:
Verified Redundant Constraints for MiniZinc. To appear in the 32nd
International Conference on Principles and Practice of Constraint Programming
(CP 2026), LIPIcs, Vol. 379, Article 53, 2026.
https://doi.org/10.4230/LIPIcs.CP.2026.53

```bibtex
@inproceedings{DanzingerMusliu2026VerifiedRedundantConstraints,
  author    = {Philipp Danzinger and Nysret Musliu},
  title     = {From LLM Suggestions to Lean Proofs: Verified Redundant Constraints for MiniZinc},
  booktitle = {32nd International Conference on Principles and Practice of Constraint Programming (CP 2026)},
  series    = {Leibniz International Proceedings in Informatics (LIPIcs)},
  volume    = {379},
  articleno = {53},
  year      = {2026},
  publisher = {Schloss Dagstuhl -- Leibniz-Zentrum f{\"u}r Informatik},
  doi       = {10.4230/LIPIcs.CP.2026.53}
}
```

## License

This software is released under the MIT License. See `LICENSE`.
