# Palomar preparation

This revision ports the archived RP²/RP³ development to Lean 4.35.0-rc2 and
Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
The original release is preserved at tag `zenodo-2026-10-21`, commit
`e8ebad84b92e4fdfd99aff2fa7619c1deb36016d`, and
<https://doi.org/10.5281/zenodo.23548847>.

## Selected statements

`Challenge.lean` imports only Mathlib. It defines the finite square-lattice
subgraph, normalized spherical reference measure, squared-inner-product
Gibbs weight, normalized quadrupolar correlation, and exact lattice infinity
distance. It advertises `ProjectiveDecay.rp2_log_square` and
`ProjectiveDecay.rp3_log_square`.

`Solution.lean` reproduces those definitions and uses the original
`RP2.log_square_quadrupolar_decay_signed` and
`RP3.log_square_quadrupolar_decay_signed` endpoints. Conversion of graph types
and unfolding of the correlation are intended to be definitional equalities;
there is no additional analytic or decay hypothesis.

The two deliberately unproved theorem bodies in Challenge are statement
placeholders for Comparator. No proof in Solution may depend on those
placeholders. `scripts/generate-palomar-interface.py --check` checks that the
independent files have exactly the shared definitions and advertised types.
This text check supplements, and does not replace, Comparator.

The entry selects the finite-volume bounds. Existing local-limit,
high-temperature, and Fourier-regularity results remain in the full libraries,
but are not separately advertised as Comparator-checked results of this entry.

## Source and audit history

The module-system port adds public imports, public declarations, and exposed
definition bodies where clients use unfolding. Fresh verification is required
for this revision; the old audit counts and hashes are historical evidence.
Generated standalone files and old executable audit sources are omitted from
this snapshot; they remain in the tagged original release. The exact omissions
are recorded in `verification/palomar-omitted-sources.json`. Every original
library module under RP2 and RP3 is retained.

The original `scripts/verify.py`, `scripts/verify_rp3.py`, bundle generators,
and archived reports describe the Lean 4.34.1 release. They are not the
verification entry points for this port. Use the commands below and the new
workflow. Do not interpret a historical PASS record as a check of this revision.

## Local checks

Install the pinned Lean toolchain, Git, Python 3, and, for the Comparator
script, Linux with bubblewrap. Run:

```sh
python3 scripts/generate-palomar-interface.py --check
python3 scripts/check-lean-sources.py
lake exe cache get
lake build
lake env lean SemanticWitnesses.lean
lake env lean RP3SemanticWitnesses.lean
lake env lean PalomarAxioms.lean
bash scripts/verify-comparator.sh
```

The two semantic witness files check the public model and normalization
interfaces. The Comparator script checks the selected statements and uses
the independent kernels bundled with the pinned toolchain. No new kernel
replay success is asserted until the corresponding run succeeds.

The preparation environment needs the original release's documented
`proc-self-compat.c` shim for executable-resource discovery. It changes no
proof term or kernel rule and is not part of the submitted library or workflow.
Ordinary Linux hosts should not need that environment-specific shim.

## Full Palomar mechanical preflight

The `Palomar preflight` GitHub workflow calls the official reusable workflow
at an immutable pipeline commit with `mode: full` and
`execution_profile: palomar-standard-v1`. Its report is the mechanical
preflight required before submission. Ordinary `lake build` and a standalone
Comparator result do not replace that report.

After the exact committed revision passes, submit
`masakioshikawa/rp2-rp3-lean`, its full 40-character commit SHA, and
`comparator.json` at <https://submit.palomar-registry.org/>. Use the repository
root as project directory. Review the resulting editorial report before
choosing registration. No submission or registration is performed by preparing
this branch.

## Current verification status

Local compilation passed for both libraries and the independent Challenge and
Solution on 22 October 2026 (America/New_York). Both semantic-witness files
compiled. Lean's axiom reports for both selected Solution theorems contain
only `propext`, `Classical.choice`, and `Quot.sound`.

All 169 library files were compared with the archived originals after reversing
the documented visibility/header edits and the single additional metrizability
import. Their mathematical statements and proof bodies are unchanged. The
source-format and interface-generation checks also passed. Logs and the local
check record are in `verification/palomar-local-2026-10-22/`.

This is still a preparation revision: the full sandboxed Comparator and official
Palomar mechanical preflight are outstanding. Do not submit it until those
checks pass. The original archived proof remains separately available.

The local preparation environment does not permit the Linux namespaces required
by bubblewrap (`Creating new namespace failed: Operation not permitted`). The
sandboxed Comparator and full preflight must therefore run on an ordinary Linux
host or through the supplied GitHub workflow. Local compilation does not replace
those checks.
