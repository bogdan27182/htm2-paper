# Sharp residual bounds in CAT(0) spaces

Lean formalization accompanying *Sharp residual bounds for anchored iterations
in CAT(0) spaces, with and without fixed points*, by Bogdan Dumitru.

## Build

Install Lean's `elan` toolchain manager, then run from this directory:

```sh
lake exe cache get
lake build
```

Lean and mathlib are pinned to version 4.33.1. `lake-manifest.json` locks
the dependency versions used by the build.

To inspect the main theorem statements and their foundational dependencies:

```sh
lake env lean Audit.lean
```

## Formalized results

All declarations are in the `Cat0Bounds` namespace.

| Result | Main declarations |
|---|---|
| General anchoring family and sharpness | `family_bound`, `family_sharpness` |
| Adaptive iteration and sharpness | `adaptive_horizon_bound`, `adaptive_sharpness` |
| Minimal-displacement convergence | `family_displacement_tendsto`, `adaptive_displacement_tendsto` |
| Endpoint asymptotic constant | `endpointWorstCase_asymptotic` |
| Stronger bounds and sharpness | `family_stronger_bound`, `adaptive_stronger_bound`, `stronger_family_sharpness`, `stronger_adaptive_sharpness` |
| Distinct initial points | `halpernFrom_bound`, `adaptiveFrom_horizon_bound` |

The proofs use explicit `Geometry` hypotheses: geodesic distance identities,
the CAT(0) comparison inequality, and quasilinearization Cauchy–Schwarz.
Their derivation from the CAT(0) definition is outside this formalization.
The real-line model and equality examples are proved within Lean. The
external oracle lower bound is also outside the formalization.
