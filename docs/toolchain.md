# Toolchain and pins

Re-check everything on this page with `make verify-toolchain` (hashes, archive ↔ installed toolchain) and
`lake env lean build/gap.lean`-style `#check` probes (the Mathlib table below was produced that way).

## Pins

| Item | Value | Checked by |
|---|---|---|
| Lean toolchain | `leanprover/lean4:v4.35.0` (`lean-toolchain`), commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` | `lean --version` |
| Toolchain archive | `lean-4.35.0-linux.tar.zst`, sha256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` | `make verify-toolchain` (`toolchain.sha256`) |
| elan installer | `elan-init.sh` at elan tag v4.2.4 (commit `227caca133724d5516bee25c2aeb3e609478f2d8`), sha256 `a620ff1641616222c8d37c54845492004bb84d6877cdbc944dd65c1aa685bf53` (identical to `master` on 2026-11-05) | `make verify-toolchain`, CI install step |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` = tag `v4.35.0` (checked with `git ls-remote`, 2026-11-05) | `lake-manifest.json` |
| Rust (tools only) | 1.97.0 (`tools/rust-toolchain.toml`), no crates (`docs/dependencies.md`) | `cargo build --locked` |

`make verify-toolchain` extracts the pinned archive and requires it to be byte-identical (`diff -r`) to the
installed toolchain. VALIDATED 2026-11-05: identical, 17 925 files.

## Checkers shipped in the archive (one trust source until one is built from source)

| Binary | sha256 | Role in `make lean-replay` |
|---|---|---|
| `lean` | `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38` | build |
| `lake` | `8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1` | build, `lake check`, `lake comparator` |
| `leanchecker` | `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` | per module; `--from-export` |
| `leanchecker-paranoid` | `ca74d1e9a856149ed05acb600d8931a574dd9f465745beeaf93e3de7b7cbe274` | `--from-export` |
| `leanexport` (lean4export 3.1.0) | `f6a6483d518a11b323c28b9bac176d2220df0e9fc3230833815db9586669c074` | export |
| `nanoda_bin` 0.4.19 | `cbf13950fc4a48f635a0beceeb5ed32dd82568b870cfd081b6391c1f2cf02ba5` | export, permitted-axiom list, hard error |
| `con-leche` | `23a32522ea2c79f4ec8b48916272b37a423bda171e57cd83cfcf142eec50e621` | export, `--verified` |
| `con-ron` | `60f4ca9fb9436c323789fa49aae33af6dcd1b9b54b43a66b461779ce79fd8eec` | export, `--verified` |
| `lean4lean` | `baaec030a70c78562ced2c75866ab0d2410e81ce680b835179ed16570ad5ef97` | only via `lake check --from-export --paranoid` |

Observed behaviour (VALIDATED 2026-11-05, commands in `docs/lessons.md` entries 2–4):
- `lake env lean4lean OscInt.Basic` prints "found a problem … incompatible header" and **exits 0**; it cannot read
  this toolchain's `.olean` files directly. It is used only inside `lake check --paranoid`, which accepted.
- `leanchecker --from-export` accepts an empty export; the replay therefore checks the export contains every
  audited theorem before any checker runs.
- Kernel-bypass control (an ill-typed `1 = 2` added by a metaprogram under `debug.skipKernelTC`): the build and
  the axiom audit accepted it (axioms: none); `leanchecker` per module, `leanchecker(-paranoid) --from-export`,
  nanoda (panic), con-leche, con-ron and `lake check --paranoid` all rejected it.
- `native_decide` adds the auxiliary axiom `<thm>._native.native_decide.ax_1_1`; the audit rejects it.

## Mathlib at the pinned commit: what the plan relies on

Present (each `#check`ed at the pin, 2026-11-05):
`intervalIntegral.integral_mul_deriv_eq_deriv_mul`, `ContDiffBump`, `SmoothPartitionOfUnity`,
`IsCompact.elim_finite_subcover`, `Metric.finite_approx_of_totallyBounded`, `ContractingWith.fixedPoint`,
`ContractingWith.fixedPoint_lipschitz_in_map`, `Real.contDiffAt_arccos`, `integral_cexp_quadratic`,
`taylor_mean_remainder_lagrange`, `taylor_mean_remainder_cauchy`,
`MeasureTheory.tendsto_integral_of_dominated_convergence`, `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`
(whole-space integration by parts), `ImplicitFunctionData` / `ImplicitFunctionData.contDiffAt_implicitFunction` (parameter in a
complete normed space), `map_add_eq_sum_add_integral_iteratedFDeriv` (multivariate Taylor, integral remainder).

Corrections to the project brief (the brief's names do not exist at the pin):

| Brief says | At the pin |
|---|---|
| `exists_smooth_zero_one_of_isClosed` | absent; use `exists_contMDiffMap_zero_one_of_isClosed` (manifolds) or `exists_contDiff_zero_iff_one_iff_of_isClosed` |
| `fourierIntegral_gaussian_pi` | absent; `fourier_gaussian_pi`, `fourier_gaussian_pi'`, `fourierIntegral_gaussian` |
| `Mathlib.Data.Real.Basic` (import path) | deprecated; `Mathlib.Basic.Real.Basic` |

Absent (no declaration or file matching, `grep -rE` over `Mathlib/`, 2026-11-05):

| Item | Status at the pin |
|---|---|
| 2D integration by parts on bounded domains (Fubini + 1D product rule) | absent (only the whole-space, integrable form above) |
| van der Corput lemma (any dimension) | absent (`van der Corput`, `VanDerCorput`: no match) |
| any stationary-phase lemma | absent |
| multivariate Taylor with remainder continuous in a parameter | absent (non-parametric integral form exists) |
| implicit function theorem with a metric-space parameter | absent (normed-space parameter only) |
| Laguerre polynomials | absent |
| Szász's Hermite-function bound | absent |
| Riesz–Thorin | absent (`Thorin`: no match) |
| discrete Hardy–Littlewood–Sobolev | absent |

Mathlib at the pin uses the module system (`module`, `public import`). OscInt files are plain (non-module) files;
this works (with a build warning) and keeps theorem bodies visible to `leanexport`. Converting upstream
candidates to module syntax is part of preparing each Mathlib PR (technical debt, `docs/upstream.md`).

## Timestamp authorities (pinned roots in `stamps/roots/`, hashes also pinned in `tools/src/bin/stamp.rs`)

| Authority | Endpoint | Root | Root file sha256 | Root expires |
|---|---|---|---|---|
| FreeTSA | https://freetsa.org/tsr | Free TSA Root CA (fetched from https://freetsa.org/files/cacert.pem, trust on first use) | `2151b61137ffa86bf664691ba67e7da0b19f98c758e3d228d5d8ebf27e044438` | 2041-03-07 |
| DigiCert | http://timestamp.digicert.com | DigiCert Trusted Root G4 (Ubuntu ca-certificates) | `ce7d6b44f5d510391be98c8d76b18709400a30cd87659bfebe1c6f97ff5181ee` | 2038-01-15 |
| Sectigo | http://timestamp.sectigo.com | USERTrust RSA Certification Authority (Ubuntu ca-certificates) | `8a3dbcb92ab1c6277647fe2ab8536b5c982abbfdb1f1df5728e01b906aba953a` | 2038-01-18 |

OpenTimestamps: digests are submitted to the `a.pool` and `b.pool` calendars; the `.ots` files are pending proofs
until upgraded with an OpenTimestamps client after Bitcoin confirmation.

## Mathlib source build

First complete run: CI run 18 (https://github.com/thomas-falk-research/lean-oscillatory/actions/runs/42131847959),
workflow_dispatch on commit 5ae5589, 2026-11-05 23:45 – 2026-11-06 01:53 UTC (about 2 h). The job compiled all 8624
Mathlib modules itself (`Mathlib modules compiled in this job: 8624`, no fetched or replayed Mathlib module), built the
library, and `make commit` found all six statement commitments equal to their pinned stamps. VALIDATED: for these
statements, the source build and the binary cache give the same elaborated statements. An earlier run (CI run 14,
commit 9cb9c11) compiled 2512 modules and then failed because `MathlibNames.lean` needs all of Mathlib; fixed.
