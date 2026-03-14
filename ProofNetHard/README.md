# ProofNet-Hard

First, set up the Lean environment and install the Python dependencies:

```bash

cd ProofNetHard
bash install_lean_env.sh
make install
```

To run a single experiment

- The python script for inference is at [pipeline/autoformalize_pipeline_new.py](pipeline/autoformalize_pipeline_new.py).
- The python script for evaluation is at [afc/proofnet/proofnet_checker.py](afc/proofnet/proofnet_checker.py).

To run batch experiments

- The python script for inference is at [experiments/scripts/batch_autoformalize.py](experiments/scripts/batch_autoformalize.py). You need to set the configurations in the script, and then run it as the following:

```bash

cd ProofNetHard
python experiments/scripts/batch_autoformalize.py
```

- The python script for inference is at [afc/proofnet/proofnet_checker.py](afc/proofnet/proofnet_checker.py). You need to run it as a module and pass the configurations as command line arguments. The following are the configurations used for our experiments:

```bash

cd ProofNetHard
python -m afc.proofnet.proofnet_checker run --root_dir "absolute path for ProofNetHard" --scan_roots "absolute path for the outputs to be evaluated" --strategies beq_plus --num_concurrency 200 --timeout 60 --worker_walltime 300 --progress --dataset DSL --gt_csv "absolute path for data/ProofNet-Lean4_proof_hard.csv"
```
