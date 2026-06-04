# Reed--Solomon Proximity Gaps — Companion Repository

Manuscripts, Lean 4 formalization, and Python verification scripts for two
papers by Raullen Chai and Xinxin Fan (IoTeX Network):

> **Paper 1 — FRI Soundness Above the Johnson Bound via Threshold Halving.**
> Cryptology ePrint Archive, Paper [2026/861](https://eprint.iacr.org/2026/861.pdf), 2026.
> Self-contained materials in [`paper1/`](paper1/).
>
> **Paper 2 — Action-Orbit FRI Soundness above Johnson:
> Universal $K$-Bounds at Ethereum-Deployed Reed--Solomon Parameters.**
> Cryptology ePrint Archive, Paper [2026/858](https://eprint.iacr.org/2026/858.pdf), 2026.
> Self-contained materials in [`paper2/`](paper2/).

The papers attack the open intermediate zone (Johnson radius $< \delta < $
list-decoding capacity) of the Reed--Solomon proximity-gap problem — the
deployment regime of every FRI-based STARK on Ethereum's roadmap.

[![CI](https://github.com/iotexproject/rs-proximity-gaps/actions/workflows/ci.yml/badge.svg)](https://github.com/iotexproject/rs-proximity-gaps/actions/workflows/ci.yml)

---

## Repository Layout

The repository is organized **per paper**: each paper directory is
self-contained.

```
rs-proximity-gaps/
  lean/                      Merged Berlekamp / V_bad codim Lean branch
    FRISoundness/Berlekamp/  Four combinatorial cores for paper 3 sections 4-5
    lakefile.toml, lean-toolchain
  scripts/                   Merged companion Python scripts for the flattened tree
  outputs/                   Saved outputs for the flattened companion tree

  paper1/
    paper.pdf                  Paper 1 manuscript
    PROOF_CHAIN.md             Step-by-step trace of Paper 1's main theorem
    lean/                      Lean 4 + Mathlib formalization
      STATUS.md                Per-theorem status board (paper label ↔ Lean identifier)
      FRISoundness/            Named theorems (zero `sorry`, zero project-level axioms)
      lakefile.toml, lean-toolchain
    scripts/                   Python verification scripts (stdlib only)
      CAVEATS.md               Methodology caveats from a public-facing audit
      deployment_params.py     Deployment parameter table generator
      proximity_gap_diagram.py Proximity-gap figure
      ca-bound/                Half- and equal-threshold CA
      fri-coupling/            FRI even/odd coupling and proximity gap
      op1-barrier/             Equal-threshold CA equals C(n,w)/|F|
      op2-obstruction/         M_max >= 2 at FRI parameters
      list-size/               Moments and pairwise / k-wise independence
      char2-circle/            Characteristic-2 / circle-FRI extensions
      cs-construction/         Crites--Stewart construction sweep
      archive/                 Earlier exploratory scripts
    outputs/                   Saved script outputs (mirrors scripts/)

  paper2/
    paper.pdf                  Paper 2 manuscript
    scripts/
      CAVEATS.md               Caveats for the deployment-scale spot checks
      deployment-l3/           Paper 2 L3 / boundary-lift / GS m=2 list-decode

  LICENSE                      Apache 2.0
```

---

## Quick start

**Build the Lean formalizations**:

```bash
cd paper1/lean
lake exe cache get   # download Mathlib cache (~5 min)
lake build           # builds FRISoundness (zero `sorry`)

cd ../../lean
lake exe cache get
lake build FRISoundness.Berlekamp  # builds the merged Berlekamp / V_bad codim tree
```

**Run a verification script**:

```bash
python3 paper1/scripts/op1-barrier/op1_scaling.py
python3 paper2/scripts/deployment-l3/issue419_action_orbit_check.py
python3 scripts/op1-barrier/op1_scaling.py
```

**Regenerate Paper 1's deployment-parameter table or proximity-gap figure**:

```bash
python3 paper1/scripts/deployment_params.py [--latex] [--per-round-max]
python3 paper1/scripts/proximity_gap_diagram.py
```

Per-script docstrings document what each script computes; methodology
caveats live in each paper's `scripts/CAVEATS.md`. Saved outputs (where
pre-computed) mirror the scripts layout under `paper1/outputs/`; redirect
stdout to refresh, e.g.
`python3 .../op1_scaling.py > paper1/outputs/op1-barrier/op1_scaling.output.txt`.

The CI workflow (`.github/workflows/ci.yml`) runs `lake build` for both Lean
trees and a sample of Python scripts on every push.

---

## Citation

```bibtex
@misc{ChaiFan2026FRI,
  author = {Chai, Raullen and Fan, Xinxin},
  title  = {{FRI} Soundness Above the {J}ohnson Bound via Threshold Halving},
  year   = {2026},
  howpublished = {Cryptology ePrint Archive, Paper 2026/861},
  url    = {https://eprint.iacr.org/2026/861},
  note   = {Companion repository: \url{https://github.com/iotexproject/rs-proximity-gaps}}
}

@misc{ChaiFan2026ActionOrbit,
  author = {Chai, Raullen and Fan, Xinxin},
  title  = {Action-Orbit {FRI} Soundness above {J}ohnson:
            Universal $K$-Bounds at Ethereum-Deployed {R}eed--{S}olomon Parameters},
  year   = {2026},
  howpublished = {Cryptology ePrint Archive, Paper 2026/858},
  url    = {https://eprint.iacr.org/2026/858},
  note   = {Companion repository: \url{https://github.com/iotexproject/rs-proximity-gaps}}
}
```

---

## License

[Apache License 2.0](LICENSE).
