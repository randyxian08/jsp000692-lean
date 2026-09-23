# JSP-000692 Lean proof project

Maintained by [randyxian08](https://github.com/randyxian08), with the AI assistance and upstream attribution documented in the [project guide](submissions/jsp-000692-randyxian08/README.md).

This dedicated public repository separates this project from the awards metadata repository. It preserves the original Git history and the first publicly named complete-proof commit `b2b873d9b62864e511bb61173021e5db8a0953b7`. The current Lean 4.34.0 proof commit is `721bef439aaa4f98b1185c4dc31060f4ae1a3ea0`. Neither the migration nor the upgrade establishes an earlier public completion date, priority, official verification, or award eligibility.

## Reproduce the selected proof

```sh
git clone https://github.com/randyxian08/jsp000692-lean.git
cd jsp000692-lean
git checkout 721bef439aaa4f98b1185c4dc31060f4ae1a3ea0
cd submissions/jsp-000692-randyxian08
python3 scripts/verify.py --prepare
```

Follow the [current project guide](submissions/jsp-000692-randyxian08/README.md) and its exact toolchain. Selected theorems: `JSP692.jsp000692_complete` and `JSP692.jsp000692_complete_explicit`.

## Scope and evidence

Both finite-hypergraph questions of Erdos 836. For every real C and rank threshold R, an r-uniform intersecting hypergraph of exact chromatic number 3 has r >= max(2,R), no isolated vertices and more than C*r^2 active vertices, refuting an eventual uniform quadratic bound. The second part proves distinct edges E,F with r <= 2*card(E intersection F)+1, hence the requested universal linear intersection bound. Counts use the union of edges and exact three-chromaticity is explicit. The original questions require neither the sharper central-binomial formula nor an infinite-family version; no such strengthening is claimed. Please review correspondence to the original finite-hypergraph setting.

Lean 4.34.0 / Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Modular and standalone compilation passed with 67 declarations audited in each; 11 verification utility tests also passed. The [current receipt](submissions/jsp-000692-randyxian08/verification/status.json) and [dated verification note](submissions/jsp-000692-randyxian08/VERIFICATION-20260923.md) record the local checks. A later [FRO comparator and nanoda self-check](submissions/jsp-000692-randyxian08/verification/2026-09-23-fro/README.md) replayed the explicit complete theorem against a separately prepared challenge in a network-disconnected Linux container.

The older Lean 4.19.0 proof commit remains an ancestor of `main`, with its historical checks preserved under `verification/run-20260916T154622Z/`. The comparator challenge imports the submitted definition layer, so neither self-check decides whether the Lean statement matches the English problem.

Formalization submitted by randyxian08 with OpenAI Codex assistance. Question 1 reuses Noga Alon's mathematical construction, credited on [Erdos 836](https://www.erdosproblems.com/836). [Liam Price's earlier post](https://www.erdosproblems.com/forum/thread/836#post-5941) reports a GPT-5.5 Pro solution of Question 2; its full manuscript has not been compared here. No mathematical discovery or first-formalization claim is made.

Original public source: https://github.com/randyxian08/awards/tree/b2b873d9b62864e511bb61173021e5db8a0953b7

Existing awards PR: https://github.com/TheJustinSunPrize/awards/pull/95

ORCID (self-linked supplementary identity evidence): https://orcid.org/0009-0003-0088-9268

Identity verification and all award decisions remain pending. This repository is the author's migration of their own contributed project, not a claim to authorship of the credited upstream mathematics or libraries.
