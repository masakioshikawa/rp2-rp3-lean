# Compilation record — 8 October 2026

This is development compilation, not a separate full mathematical or
axiom-dependency audit. Full auditing has not started.

## Toolchain

- Lean 4.34.1.
- mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Upstream adapted source commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Modular project

All 55 imported proof modules, and the public `RP2.lean` entry point, compiled
successfully. Modules were checked sequentially with `lake env lean -j1
-DElab.async=false`, writing local `.olean` files for their successors. The
public entry point exited **0**, with no compiler diagnostics.

`module-checks.json` records the source SHA-256 values of all 56 checked
modules, including the entry point. Earlier failed development attempts and
old audit logs from the supplied partial project are not included here.

## Standalone file

Command:

```sh
lake env lean -j1 -DElab.async=false RP2-Formalization.lean
```

The full generated source was also compiled with an output `.olean` path.
Result: **exit code 0**. The check took approximately 406 seconds and emitted
routine linter/deprecation warnings, with no compiler errors. The complete
output is in `standalone.log`.

- Source length: 10,967 lines.
- Source SHA-256: `9ddd73a461e8880a042fdfcf3f4989c6fbcaf7007c5a6eb53267d5635462f64f`.
- Peak observed process memory: approximately 6.42 GiB.

The delivered standalone source is byte-identical to the successfully checked
source. It imports only `Mathlib`; the modular source and generator are supplied
in the project archive. `AxiomAudit.lean` has been prepared for a later audit
but has not been executed for this development.
