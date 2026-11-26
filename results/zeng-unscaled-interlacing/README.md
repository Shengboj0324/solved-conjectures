# Zeng’s unscaled interlacing question

**Lean status:** none.

Jiang Zeng asks whether consecutive original rows of his two-parameter Narayana kernel have strictly interlacing negative zeros. The [proof](proof.md) gives a stronger bound for every degree, every $0<q<1$ and every $\theta>-1$. If $r_{n,i}$ is the $i$th smallest root magnitude, then

```math
r_{n+1,i}<r_{n,i}<q^2r_{n+1,i+1}.
```

The argument factors the coefficients into simple dilations and uses the reciprocal symmetry of each original row. Independent mathematical review is requested in the tracking issue. [Version 2, closing question 1](https://arxiv.org/abs/2610.28691v2) · [Source audit](sources.md) · [Issue 792](https://github.com/1337isnot1337/solved-conjectures/issues/792)

Run `python3 results/zeng-unscaled-interlacing/check.py` from the repository root. Exact signed polynomial remainders test both strict interlacings, including the factor $q^2$, with rational parameters. [Verifier](check.py)

## Citation

If you use this proof or its exact check, please credit Cinna Davis and GPT-6.2 Astra, cite this proof and the project, and cite Jiang Zeng for the kernel and original question. [Cinna Davis](https://itsdavis.com/) · [Proof record](https://github.com/1337isnot1337/solved-conjectures/blob/01123eea5516ad43f09d92173d8cefed0e9ae190/results/zeng-unscaled-interlacing/proof.md) · [Zeng’s paper](https://arxiv.org/abs/2610.28691v2)
