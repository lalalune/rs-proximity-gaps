# Saved Outputs

Stable, reproducible outputs of the canonical scripts under `../scripts/`.
Each subdirectory mirrors `../scripts/`. Re-running the corresponding script
should produce a textually similar (timestamps and floating-point ULPs aside)
output.

Topics:

| Directory | Mapped scripts | Paper claim verified |
|---|---|---|
| [`ca-bound/`](ca-bound) | `scripts/ca-bound/audit_*.py`, `scripts/ca-bound/ca_*.py` | Theorems on half- and equal-threshold CA |
| [`cs-construction/`](cs-construction) | `scripts/cs-construction/cs_sweep_fast.py` | Crites–Stewart construction sweep |
| [`fri-coupling/`](fri-coupling) | `scripts/fri-coupling/audit_fri_coupling.py` | Lemma fri-coupling |
| [`list-size/`](list-size) | `scripts/list-size/M_errorpattern.py`, `scripts/list-size/large_n_verify.py` | Worst-case M_max growth (intermediate zone) |
| [`op1-barrier/`](op1-barrier) | `scripts/op1-barrier/op1_*.py` | Equal-threshold CA = C(n,w)/\|F\| |
| [`char2-circle/`](char2-circle) | `scripts/char2-circle/s3_char2.py` | Characteristic-2 coupling |
| [`archive/`](archive) | (no current scripts) | Outputs of earlier exploratory phases — not required for any paper claim. |

Reproduce any output:

```bash
python3 scripts/<topic>/<script>.py | tee outputs/<topic>/<script>.output.txt
```
