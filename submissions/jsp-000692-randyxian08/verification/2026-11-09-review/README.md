# Submitter-side mathematical and scope review — 2026-11-09

Selected proof A: `721bef439aaa4f98b1185c4dc31060f4ae1a3ea0` in this repository. This dated supplement adds evidence only; it does not change the selected proof or create an earlier completion timestamp. It is an AI-assisted submitter-side review, not independent human review, organizer acceptance, identity approval, or a priority/award decision.

## Result and scope

The finite-hypergraph arguments for **both** main questions were checked step by step; no blocking error was found in that scope. Question 1 formalizes Alon's credited construction, with exponentially many active vertices, no isolated padding, and a quantified refutation of any eventual quadratic bound. Question 2 proves the stronger integer conclusion `r ≤ 2 * |E ∩ F| + 1` for two distinct edges of an intersecting, uniform, non-two-colourable finite hypergraph, for `r ≥ 2`. In particular a single constant `1/3` works for the linear-intersection question.

The selected Lean theorem quantifies finite hypergraphs over `Fin n`. The [original main question](https://www.erdosproblems.com/836) does not explicitly state finiteness in its text. Extension of Question 2 to arbitrary families of finite edges follows mathematically by two-colouring compactness, but that reduction is **not included in proof A**. If the canonical target requires this broader scope, the formalization is correspondingly incomplete. No claim is made to the stronger background conjecture of an intersection of size `r − O(1)`.

## Mathematical check of Question 2

Fix an edge E and choose a largest vertex set R whose only contained edge is E. Such R exists because the vertex set is finite and uniformity makes R=E feasible. Maximality gives, for each y outside R, an edge F_y different from E contained in R∪{y}. For each x in E, R\{x} is independent. Non-two-colourability supplies an edge G_x in its complement; intersection with E forces G_x∩R={x}. The G_x are therefore distinct.

Suppose all distinct-edge intersections have size at most s. Fix x₀ in E and form an (r−1)-square matrix with rows E\{x₀}, columns G_x₀\{x₀}, and entry 1 iff y∈G_x. Each row has at most s ones, by intersection with G_x₀. If an entry is zero, the intersection of G_x and F_y can only be the point x, so x∈E∩F_y. Each column has at most s zeros, since F_y≠E. Counting all entries gives (r−1)²≤2s(r−1), hence r≤2s+1. Taking an integer bound for all intersections proves the stated witness theorem. The r=3 Fano-plane example is consistent with the `(r−1)/2` bound; this is not a claim of `r/2` at every rank.

See [LinearIntersection.lean](../../JSP692/LinearIntersection.lean) and [MATHEMATICS.md](../../MATHEMATICS.md) at proof A. Relative paths in this supplement are documentation conveniences; the immutable selected proof is A above.

## Fresh execution evidence

- `python3 scripts/verify.py --prepare`: exit 0, `PASS_LEAN_AND_AXIOM_AUDIT`; modular build, standalone re-elaboration, statement checks and all 67 axiom reports passed on Lean 4.34.0 / Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
- Each final theorem reported only `propext`, `Classical.choice`, `Quot.sound`.
- `lake env lean ReviewStandard.lean`: exit 0. The attached [audit harness](ReviewStandard.lean.txt) proves equivalence of the project's proper-colouring predicate to the conventional absence of monochromatic edges for uniform rank ≥2, and restates the integer Question 2 result in those conventional predicates. It is additional audit source, not part of proof A.
- `lake env leanchecker JSP692`: exit 0, empty output. This replays with Lean's own kernel; it is not an independently implemented checker.
- The eight original mathematical module blobs and SHA-256 digests were checked against A and were unchanged; see [receipt.json](receipt.json).

Mathlib's matching precompiled dependency cache was used; this run did not rebuild all Mathlib source. No fresh FRO or nanoda run is claimed. The [historical comparator evidence](../2026-09-23-fro/README.md) has its own date and limitations. The fresh checks above ran locally, not as an organizer-run or separately isolated audit. Logs replace absolute local paths with placeholders; the receipt hashes describe the published sanitized files.

## Attribution and administrative limits

Alon's Question 1 credit and the earlier Liam Price / GPT-5.5 Pro Question 2 report remain disclosed. The linked Overleaf manuscript was not readable during this review; no conclusion about equivalence, independent discovery or mathematical priority follows. Proof correctness, original-problem scope, code attribution, first public completion, identity, and award eligibility are separate questions.

PR #95 remains closed and unmerged. Claim #50 is closed; this supplement requests focused mathematical/scope review in the existing PR, not reopening that claim or reserving an award queue position. Repository ownership alone does not establish authorship or verified identity.
