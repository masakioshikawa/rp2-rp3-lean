SOFTWARE-ARCHIVE PACKAGING ADDENDUM — 21 October 2026

The original audit evidence below is retained as a historical record.
The nested original source ZIP and publication-build checks are omitted
from this software-only distribution. The retained checks, checker
sources, and audit report are byte-identical to their archived originals.
The project at ../../ supplies the current combined RP2/RP3 sources.
Its RP2 modules, entry point, and standalone source match the original
audited RP2 archive byte for byte. The historical RP2 lakefile.toml
differs because the later combined release also declares the RP3 target;
that existing configuration is covered by the 12 October RP3 record.
The original README follows unchanged; references to input/ and
publication-checks/ describe the earlier, unabridged evidence bundle.

--------------------------------------------------------------------

RP2 v0.4.0 fresh audit evidence, 9 October 2026

VERDICT: PASS. Read rp2-v0.4-audit.txt for findings and limitations.

input/rp2-lean-v0.4.0.zip is the original supplied archive, unchanged.
Original archive SHA-256: b6285cfc4b685e1f888b97728a62abc75f398095d43fdf57b7e9b26e2b7c2848
Separate original standalone SHA-256: 843e4759583ab05a60e0b5d25cd36fe7a3df432f0411447bdb44a15ebc26b5ad
The standalone attachment was verified byte-identical to the archive bundle.

checks/full/ contains fresh compilation, dependency inventory, kernel replay,
and summary records. All 86 project modules, the 69 public roots and their
53,315-declaration closure were checked. The standalone was also compiled
fresh and replayed. Only propext, Classical.choice and Quot.sound are axioms.

checks/NewSemanticWitnesses.lean independently spells out both new endpoints
as normalized spherical integral quotients. checks/new-semantics.json and
.log record its successful compilation. The initial witness diagnostic is
retained with an explanatory development note; no supplied proof was changed.

checker/ duplicates the relevant source/configuration from the supplied archive
for convenient inspection. Its complete original project is in input/.
publication-checks/ records the revised manuscript's build and visual review.

Reproduce in the unpacked original project, with its pinned Lean toolchain:
  python3 scripts/verify.py --fetch-cache --standalone --replay --replay-standalone --inventory

To run the additional witnesses, copy NewSemanticWitnesses.lean into a
separate directory, then from the compiled project's root run:
  lake env lean -j1 --root=/absolute/audit-dir /absolute/audit-dir/NewSemanticWitnesses.lean

This environment needed the archive's verification/runtime/proc-self-compat.c
shim for executable discovery. This is not normally needed on a conventional
Linux host. It does not change proof terms or the kernel. See the audit report.
Toolchain binaries, Mathlib caches, and newly compiled objects are omitted.
Both replays use Lean's kernel, not a separately implemented checker.
