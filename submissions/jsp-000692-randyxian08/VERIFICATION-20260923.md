# Lean 4.34.0 verification of JSP-000692

This record concerns the two-question theorem `JSP692.jsp000692_complete` and its expanded counterpart `JSP692.jsp000692_complete_explicit`. It is submitter-run evidence, not organizer verification, independent mathematical review, formalization priority, identity approval, or an award.

- Toolchain: `leanprover/lean4:v4.34.0` (compiler commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`).
- Mathlib: tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependency revisions are recorded in `DEPENDENCIES.lock.json` and `lake-manifest.json`.
- Reproduction from this project directory: `python3 scripts/verify.py --prepare`, or `python3 scripts/verify.py` after fetching the pinned cache. The source scan, modular `lake build JSP692`, 67 transitive `#print axioms` reports, statement inspection, and independently elaborated standalone `JSP000692.lean` all passed. The [machine receipt](verification/status.json) and its [dated run](verification/run-20260923T112937Z/status.json) record exact commands and output links.
- The two final theorems and all 65 other requested declarations depend only on subsets of `propext`, `Classical.choice`, and `Quot.sound`. No requested axiom report was missing; the source scan found no `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide` in proof code.
- `lake env leanchecker JSP692` exited 0, replaying the selected module in Lean's kernel. This is a same-kernel check, not an independent second implementation.
- Eleven verification utility tests and the finite regression program passed. They support the script and finite examples, not the full mathematical proof.

The Lean 4.19.0 to 4.34.0 migration changes only pinned dependencies, verification metadata and renamed Finset lemmas in the proof source. The standalone file was regenerated from the modules. The target statements and mathematical attribution are unchanged. The historical 4.19.0 records remain available under `verification/run-20260916T154622Z/` and `verification/publication-review.json`.

The original-problem correspondence and formalization authorship still require independent review. The comparator sandbox and an external kernel have not been run for this revision at the time of this source verification note; later evidence, if produced, must identify the exact proof commit separately.
