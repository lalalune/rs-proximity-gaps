# Archived Scripts

Exploratory scripts from earlier phases of this project, retained for
provenance. They are **not** required to reproduce any result in the paper —
the canonical scripts that map to specific theorems live one directory up.

| Archived script | Superseded by | Reason |
|---|---|---|
| `list-size/M_distribution.py` | `list-size/verify_E_Mtrue.py` | Histogram of M; subsumed by exact moment script. |
| `list-size/M_exact_small_p.py` | `list-size/verify_M_true_pdep.py` | Early "smallest-p" optimization. |
| `list-size/M_fast.py` | `list-size/M_errorpattern.py` | Early NumPy version of error-pattern enum. |
| `list-size/M_vs_n_studio.py` | `list-size/large_n_verify.py` | Early M_max-vs-n sweep. |
| `list-size/mmax_vs_p.py` | `list-size/verify_M_true_pdep.py` | Early M_max-vs-p sweep. |
| `list-size/pairwise_rank.py` | `list-size/verify_c2_pairwise_independence.py` | Early rank-of-pairs exploration. |
| `list-size/pairwise_rank_deep.py` | `list-size/verify_c2_pairwise_independence.py` | Deep rank-structure analysis. |
| `list-size/Rw_independence.py` | (research note) | Early test of \|R_w\| independence from syndrome. |
| `list-size/list_size_vs_p.py` | `list-size/verify_M_true_pdep.py` | Early M-vs-p sweep. |
| `list-size/c2_analysis.py` | `list-size/c2_moment_bound.py` | Failure-pattern analysis at c=2. |
| `list-size/factorial_moment_verify.py` | `list-size/verify_E_Mtrue.py` | Poisson-approx factorial moments. |
| `list-size/kwise_independence.py` | `list-size/verify_kwise_independence.py` | Early version (before refutation finding). |
| `fri-coupling/fri_folding_fixed.py` | `fri-coupling/fri_folding.py` | Earlier iteration. |
| `char2-circle/verify_char2_gpu.py` | `char2-circle/s3_char2.py` | Apple-MPS GPU version (CPU script suffices). |
