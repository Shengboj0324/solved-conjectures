# Lean verification of the plane-partition Turán conjecture

For every real $x\ge 1$ and each integer $n\ge12$, Lean proves the strict inequality

```math
P_{n-1}(x)P_{n+1}(x) < P_n(x)^2.
```

Here the polynomials are the original coefficients of the exponential series with divisor-square weight. Lean derives their recurrence by formal differentiation and proves positivity at every positive real parameter. [Heim, Neuhauser and Tröger, Conjecture 2](https://link.springer.com/article/10.1007/s00026-022-00604-4) · [Series and recurrence](../../lean/Conjectures/HeimNeuhauserPlanePartition.lean) · [Full theorem](../../lean/Conjectures/HeimNeuhauserPlanePartitionTheorems.lean).

For indices 12 through 250, the proof computes two integer evaluations of each shifted polynomial $B_n(t)=n!P_n(1+t)$, at one and at $2^{4096}$. Lean checks the factorial-cleared recurrence independently for both tables. The unit evaluation bounds every coefficient and prevents carries at the larger base. Comparing the digits proves a coefficientwise inequality, and comparing the units gives a strictly positive constant. Positive factorial factors cancel to give the displayed inequality for every real $x\ge1$. [Scalar recurrence](../../lean/Conjectures/HeimNeuhauserPlanePartitionScalar.lean) · [Certificate interpretation](../../lean/Conjectures/HeimNeuhauserPlanePartitionCertificate.lean).

Before each recurrence check, the index modules rewrite the nested sum with a proved identity. The new form makes one pass over the stored table and computes the divisor-square sums by plain recursion. This keeps the kernel within the `-M4500` memory cap that `lake build` applies on Linux runners. The certificate statements are unchanged. [Kernel-friendly recurrence](../../lean/Conjectures/HeimNeuhauserPlanePartitionFastSum.lean).

For every index from 251 onward, Lean chooses the unique saddle radius and proves exact Fourier inversion for the original coefficients. On the normalized frequency interval from 0 to 2 the integral exceeds two fifths. Its contribution between 2 and 3 is nonnegative. The third-moment bound follows from 60 rational radius intervals and an analytic estimate at large radii. A grid of 63 radius intervals and 72 frequency intervals bounds the contribution from 3 to 12 below by minus three tenths. The remaining integral is at least minus one tenth. The sum is strictly positive. The proof transfers that strict sign back to the original polynomial coefficients. [Third moment](../../lean/Conjectures/HeimNeuhauserPlanePartitionThirdMoment.lean) · [Middle frequencies](../../lean/Conjectures/HeimNeuhauserPlanePartitionMiddleIntegral.lean) · [Remaining frequencies](../../lean/Conjectures/HeimNeuhauserPlanePartitionOuterIntegral.lean) · [Turán tail](../../lean/Conjectures/HeimNeuhauserPlanePartitionTuranTail.lean).

The separate Python check reproduces all 901 rational enclosures of the written proof. The formal proof uses the interval bounds linked above. [Written proof](PROOF.md) · [Original Fourier certificate](heim-neuhauser-fourier-certificate.py).

The strict build and stock-kernel replay covered 57 project modules. The axiom audit checked all 2,611 declarations, including 2,463 theorems and 1,898 private declarations. All 67 required endpoints passed. [Joint verification receipt](verification/lean-receipt.json).

After the change to the recurrence checks, the same command was rerun locally on macOS. It covered 58 project modules and 2,642 declarations, including 2,486 theorems and 1,909 private declarations. All 67 endpoints passed, using only `propext`, `Classical.choice` and `Quot.sound`. [Rerun receipt](../../docs/verification/heim-neuhauser-fastsum-20261126/receipt.json).

To repeat the verification from the repository root, run

```bash
receipt=results/heim-neuhauser-troeger-plane-partition-turan/verification/lean-receipt.json
mapfile -t endpoints < <(jq -r '.required_endpoints[]' "$receipt")
args=()
for endpoint in "${endpoints[@]}"; do
  args+=(--require "$endpoint")
done
python3 scripts/verify_lean_target.py --root Conjectures.HeimNeuhauserPlanePartitionTheorems \
  "${args[@]}" --per-module-replay --out /tmp/plane-partition-verification
```

If you use the result, please credit the conjecture's authors and cite both Cinna Davis’s site and the exact proof or verification record you used. [Cinna Davis](https://itsdavis.com/) · [Result and verification records](https://github.com/1337isnot1337/solved-conjectures/tree/main/results/heim-neuhauser-troeger-plane-partition-turan).
