# modal-catuskoti-lean
A Github repository containing the Lean 4 formalization of the paper: "The Modal Catuṣkoṭi: Formalizing Emptiness in Classical Modal Logic," generated and verified using Aristotle (Harmonic). Aristotle is an AI theorem-proving tool that generates formal proofs that are verified in Lean 4, a proof assistant whose kernel mechanically checks each logical step. All proofs are machine-checked with no unproven assumptions.

## Implementation update

The initial repository version implemented the bivalent modal core of the construction but applied the higher-level bivalent reduction at the atomic level as well. The current version corrects the implementation so that atomic propositions receive genuinely four-valued assignments (t, f, b, n), while complex formulas retain the bivalent semantics specified in the paper.

This correction brings the Lean artifact into exact agreement with the two-tier semantics already stated in the article. It does not alter the formal results: T(P) remains satisfiable in K, T, S4, and S5; every finite iteration T^n(P) remains satisfiable in K, T, and S4; and T(T(P)) remains unsatisfiable in S5. All proofs are kernel-checked and contain no "sorry" or "admit".
