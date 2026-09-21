# JSP-000692 Lean proof project

Maintained by [randyxian08](https://github.com/randyxian08), with the AI assistance and upstream attribution documented in the [project guide](submissions/jsp-000692-randyxian08/README.md).

This dedicated public repository separates this project from the awards metadata repository. It preserves the original Git history and selected proof commit `b2b873d9b62864e511bb61173021e5db8a0953b7`. The migration itself does not establish an earlier public date, priority, official verification, or award eligibility.

## Reproduce the selected proof

```sh
git clone https://github.com/randyxian08/jsp000692-lean.git
cd jsp000692-lean
git checkout b2b873d9b62864e511bb61173021e5db8a0953b7
cd submissions/jsp-000692-randyxian08
```

Follow the version-pinned [original build guide](https://github.com/randyxian08/awards/blob/b2b873d9b62864e511bb61173021e5db8a0953b7/submissions/jsp-000692-randyxian08/README.md) and its exact toolchain. Selected theorem: `JSP692.jsp000692_complete; JSP692.jsp000692_complete_explicit`.

## Scope and evidence

Both finite-hypergraph questions of Erdos 836. For every real C and rank threshold R, an r-uniform intersecting hypergraph of exact chromatic number 3 has r >= max(2,R), no isolated vertices and more than C*r^2 active vertices, refuting an eventual uniform quadratic bound. The second part proves distinct edges E,F with r <= 2*card(E intersection F)+1, hence the requested universal linear intersection bound. Counts use the union of edges and exact three-chromaticity is explicit. The original questions require neither the sharper central-binomial formula nor an infinite-family version; no such strengthening is claimed. Please review correspondence to the original finite-hypergraph setting.

Lean 4.19.0 / Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. Modular and standalone compilation passed with 67 declarations audited in each. The source-bound `verification/status.json`, `verification/publication-review.json`, and logs under `verification/run-20260916T154622Z/` record the evidence. Dependency caches were reused; 11 verification utility tests passed.

These are historical checks of the selected proof version, not a new Lean run at the documentation-only migration commit. The selected proof commit is retained as an ancestor of `main`, and all project bytes are unchanged by the repository migration.

Formalization submitted by randyxian08 with OpenAI Codex assistance. Question 1 reuses Noga Alon's mathematical construction, credited on [Erdos 836](https://www.erdosproblems.com/836). [Liam Price's earlier post](https://www.erdosproblems.com/forum/thread/836#post-5941) reports a GPT-5.5 Pro solution of Question 2; its full manuscript has not been compared here. No mathematical discovery or first-formalization claim is made.

Original public source: https://github.com/randyxian08/awards/tree/b2b873d9b62864e511bb61173021e5db8a0953b7

Existing awards PR: https://github.com/TheJustinSunPrize/awards/pull/95

ORCID (self-linked supplementary identity evidence): https://orcid.org/0009-0003-0088-9268

Identity verification and all award decisions remain pending. This repository is the author's migration of their own contributed project, not a claim to authorship of the credited upstream mathematics or libraries.
