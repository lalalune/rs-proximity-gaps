/-
Copyright (c) 2026 Raullen Chai, Xinxin Fan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Berlekamp / V_bad codim — umbrella module.

Companion to *Closing the FRI Soundness Gap: A Sequence-School Approach*
(Chai & Fan, 2026), §3–§5. The four load-bearing combinatorial cores
behind the rigorous unconditional bound `codim V_bad = 2(c − 1)` for
all `c ≥ 2`, all deployment `D`, are split across:

  * `Berlekamp/Defs.lean`              — preimage size, `RealizerData`.
  * `Berlekamp/PreimageCounting.lean`  — paper Lemma 5.1 (Note 0119).
  * `Berlekamp/SupportSubstitution.lean` — paper Lemma 5.2 (Note 0122).
  * `Berlekamp/VSInclusion.lean`       — paper Theorem 4.1 (Note 0117).
  * `Berlekamp/CrossRatioCount.lean`   — paper Lemma 5.3 (Note 0123).
  * `Berlekamp/Main.lean`              — composition + codim interface.
-/
import FRISoundness.Berlekamp.Defs
import FRISoundness.Berlekamp.PreimageCounting
import FRISoundness.Berlekamp.SupportSubstitution
import FRISoundness.Berlekamp.VSInclusion
import FRISoundness.Berlekamp.CrossRatioCount
import FRISoundness.Berlekamp.Main
