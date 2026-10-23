# Software-only packaging record — 21 October 2026

This archive contains the complete combined RP²/RP³ Lean source release,
its reproducibility tools, and the available verification evidence.
The Lake package version remains 0.4.0. The packaging date identifies this
distribution, without changing the mathematical release or its proof status.

## Origin

The parent `rp3-lean.zip` has SHA-256
`5755419666169b34cce016ee51b6b308354b5f1248a1da9830aea59abce60181`.
All 690 entries in its supplied `SHA256SUMS` were checked successfully.
That checksum inventory is retained in
`verification/packaging/parent-SHA256SUMS` as historical evidence, including
entries for files intentionally omitted from this edition.

The additional RP² audit evidence comes from `rp2-v0.4-verification.zip`,
dated 9 October 2026. Its checks, checker sources, and audit report are retained
under `verification/rp2-audit-2026-10-09/`. Its README has a packaging addendum.
The duplicated source ZIP and manuscript-build checks in that evidence bundle
are omitted. The parent archive hashes and exact imported/omitted file hashes
are recorded in `verification/packaging/manifest.json`.

## What changed

- Omitted `analytical-addendum/` and `analytical-rp3/`, including all historical
  analytical PDFs, TeX, expository Markdown, and their threshold calculations.
- Updated `README.md`, `README-RP3.md`, and the preface of
  `REVIEW-RESPONSE.md` to describe this distribution accurately.
- Added the separate RP² audit evidence, this packaging record, and a machine-
  readable comparison manifest; regenerated the top-level `SHA256SUMS`.

Every original `.lean` file is retained byte for byte. All active build,
bundle-generation, dependency-pin, semantic-baseline, and proof-verification
files are unchanged. `LICENSE` and `NOTICE` are unchanged. The historical
review text in `review/` is retained for the code attribution required by
`NOTICE`; it is not imported by the verified libraries. Historical comments
and logs can still refer to the separately circulated analytical notes.

## Checks performed for this packaging

- ZIP integrity and the original release's complete checksum inventory.
- Byte equality for every retained original file except the three documentation
  edits and the regenerated checksum inventory.
- All 188 files in the final 12 October RP³ verification source snapshot.
- All 85 RP² proof modules, its public entry point, and its standalone source
  against the original RP² source ZIP preserved in the 9 October audit bundle.
- Both standalone files regenerated in memory and compared with their delivered
  source, using the unchanged `bundle.py --check` and `bundle_rp3.py --check`.
- Both verification scripts' dependency-pin/configuration checks and complete
  project import-closure discovery, without invoking Lean.
- The original RP³ semantic inventory against its unchanged reviewed baseline.
- Fresh extraction of the final ZIP, every new checksum, and both bundle checks.

These are packaging and source-identity checks. No new Lean compilation,
semantic elaboration, kernel replay, or human mathematical audit was performed
on 21 October. Lean and Lake are not installed in the packaging environment.
The previous audit evidence continues to concern exactly the unchanged proof
sources. The added audit checker copies are evidence, not extra library imports.

The 9 October RP² audit used an RP²-only `lakefile.toml`; its one historical
configuration difference from the combined release is expected. The combined
configuration was already present in, and checked by, the 12 October RP³ run.
It has not been changed by this packaging.

## Proof source identities

RP2-Formalization.lean:
`843e4759583ab05a60e0b5d25cd36fe7a3df432f0411447bdb44a15ebc26b5ad`

RP3-Formalization.lean:
`f0b6d06374f5565842bdf30620a715f1e854dbe992c5eeb5f850bdac034f43d9`

The ZIP has a new hash because its documentation and packaging changed.
The two proof-source hashes above remain those cited in the manuscript.

## Reproduction

From this directory, verify the packaged bytes before generating new outputs:

```sh
sha256sum --check SHA256SUMS
python3 bundle.py --check
python3 bundle_rp3.py --check
```

With the exact pinned toolchain and dependencies, the full proof checks are:

```sh
python3 scripts/verify.py --fetch-cache --standalone --replay --replay-standalone --inventory
python3 scripts/verify_rp3.py --fetch-cache --standalone --replay
```

Run those commands sequentially. The verification scripts write fresh records
under `verification/latest/` and `verification/rp3-latest/`. Do not regenerate
the RP³ semantic baseline during ordinary verification. The pinned Lean and
Mathlib versions, available memory requirements, and theorem scopes are
described in the two READMEs. Dependencies are pinned, not vendored.

The archived RP³ run replayed its public dependency closure and separately
compiled its standalone file; it did not additionally replay the standalone
object. The archived RP² audit includes both replay routes. All recorded
replays use Lean's own kernel. This packaging does not add an independent
kernel check or a hosted CI run.
