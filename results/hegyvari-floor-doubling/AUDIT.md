# Scope and independent audit

[Steve Fan, arXiv:2607.14071v6, §1 and Remark 4.2](https://arxiv.org/html/2607.14071v6) states Hegyvári’s stronger version of the two-ray problem and credits Hegyvári’s one-dyadic case. The [Kohlmeyer–Kruer paper](https://hexagonmath.org/2611.00768v1) established the irrational-ratio doubling conjecture. Only the missing rational domain and the resulting full Hegyvári statement are claimed here; variable bases and Fan’s separate density threshold are not included.

Independent audit checked the exact source hypotheses of the transport and carry theorems, stable bits for non-dyadic ratios, the new integer-part mark in the odd-ratio case, and the passage from indexed sums to distinct values after deletion. The argument uses the work of Kohlmeyer and Kruer as a cited theorem and does not reverify their Lean formalization. Their paper is an unrefereed preprint stated for irrational ratios, so its Lean formalization covers only that case. The versions of their Propositions 5.6 and 7.1 with *non-dyadic* in place of *irrational*, used in both cases of the proof, are argued on paper in [Non-dyadic quotients](PROOF.md#non-dyadic-quotients) and are not covered by that formalization.

No Lean, external review or absolute priority claim is made.
