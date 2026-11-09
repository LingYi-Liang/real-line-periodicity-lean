# Lean checks for periodicity on the real line

This repository accompanies two preprints by Jiahui Liang.

1. [Periodicity and finite spectral types for sets of finite measure on the real line](https://doi.org/10.5281/zenodo.22988608).
2. [Periodicity of tilings by sets of finite measure on the real line](https://doi.org/10.5281/zenodo.23106559).

## What is formalized

| Source in the preprints | Lean proof |
| --- | --- |
| Spectral periodicity, Lemma 3.1 | [`SpectralWindow.lean`](Periodicity/SpectralWindow.lean) proves the two-sided finite Gram quadratic form estimate from the diagonal and off-diagonal row and column bounds. It also checks positivity of the lower constant and the strict contraction parameter. |
| Level-one tiling periodicity, Proposition 3.1 | [`TilingWindow.lean`](Periodicity/TilingWindow.lean) proves the weighted pointwise estimate, its integral cutoff loss, and the two-sided window bounds from the packing identities and the two error bounds. |
| Both preprints, equations (4.13)–(4.14) | [`FactorialBounds.lean`](Periodicity/FactorialBounds.lean) proves the induction from the binomial recurrence to the factorial bound for derivative moments. |
| Both preprints, Lemma 5.5 and the concluding dynamical argument | [`Dynamics.lean`](Periodicity/Dynamics.lean) proves existence of a distinct one-sided asymptotic pair in an infinite compact expansive system. It also proves the common-period and finite orbit representative conclusions from the phase map, expansivity, and one-sided uniqueness. |

The formalization covers the statements in the table. The Fourier
constructions supplying the window hypotheses, the derivation of the
derivative recurrence, and the analytic one-sided uniqueness theorems
remain in the preprints. The dynamical theorem takes compactness,
the phase map, expansivity, and one-sided uniqueness as explicit hypotheses.

## Build

Install Lean via [elan](https://github.com/leanprover/elan). The
toolchain and the mathlib revision are pinned in the repository.

```sh
lake exe cache get
lake build
```

The root module checks that the listed theorems depend only on
`propext`, `Classical.choice`, and `Quot.sound`.
The code is available under the [MIT License](LICENSE).
Codex assisted with the formalization.
