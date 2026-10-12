# Lean proofs for the order-independent aggregation core

The development uses core Lean 4 (v4.34.1) without Mathlib and contains no `sorry`.
The proof scripts were written with AI assistance. The Lean kernel checks every proof.
`lake build` takes about 3 s. `lake env lean Axioms.lean` prints the axioms on which each theorem
depends; every theorem uses `propext` only, or no axiom.

## Theorems

- `Lifeline.perPeer_enough`. The per-peer sums mod 3 suffice for retain and for every revoke(S), for histories and continuations of any length.
- `Lifeline.total_separates`, `Lifeline.total_not_enough`. The total sum alone does not suffice. The separating pair is "A adds 1" versus "B adds 1", followed by revoke of A.
- `Lifeline.dropA_not_enough`, `Lifeline.dropB_not_enough`. Neither per-peer sum suffices alone; the two are therefore irredundant.
- `Lifeline.perPeer_classes_L3`. Histories of up to 3 steps fall into 9 per-peer classes (by `decide`). An `#eval` also yields 9 ground-truth classes (L=3, K=2), in agreement with `congruence.py`.
- `Lifeline.Def1.no_change_is_compiler_correctness`. Without a change, and with the interpreter's own output as the only allowed output, Definition 1 reduces to compiler correctness. The proof is `Iff.rfl`; the theorem checks the modelling and is not a substantive result.

## Correspondence with congruence.py and the proposal

The model follows `pol_retain` and `pol_revoke` (Pi_base). Events are pairs (peer, value mod 3).
A policy is applied to the history followed by the continuation, as in `gt_classes`.
`Enough` and `Separates` follow Definition 2 of Part II of the proposal. Allowed sets are singletons
because the Python policies are functions. The theorems extend the bounded 9-class result for
P1/Pi_base to histories and continuations of unbounded length.

## Not proved

- The derivation itself (`derive_retained_state`, rules, recipes). The theorems concern the per-peer summary, whose 9 classes coincide with the derived result for P1/Pi_base. The derivation is checked only by the Python tools.
- The order-dependent case (Pi_hist, `after_r`, 79 classes).
- Topologies with revisions, more peers or other value domains.
