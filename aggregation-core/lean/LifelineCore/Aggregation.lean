/-
Order-independent aggregation core of congruence.py (Pi_base = retain and revoke(S)).

Abstractions relative to congruence.py.
* A history and a continuation are lists of events (peer, value mod 3), as in ALPHABET.
  Lengths are unbounded here, while Python bounds them by L and K.
* The change is the departure of a peer set S. As in pol_revoke, the policy is applied
  to the whole sequence h ++ k, so the continuation may contain further contributions.
* Python policies are functions, so each allowed set is a singleton {out p (h ++ k)}.
  Definition 2 is nevertheless stated with a transition f and allowed sets. Disjointness
  of singletons is inequality of outputs.
* The IR, the rules and the derivation (derive_retained_state) are not modelled.
-/
namespace Lifeline

inductive Peer | A | B
  deriving DecidableEq, Repr

abbrev Event := Peer × Fin 3
abbrev Hist := List Event

/-- Sum of the values whose peer satisfies `keep`. -/
def total (keep : Peer → Bool) : Hist → Fin 3
  | [] => 0
  | (p, v) :: h => (if keep p then v else 0) + total keep h

/-- The repair policy after a peer set `S` leaves. -/
inductive Policy
  | retain
  | revoke (S : Peer → Bool)

/-- Which peers' contributions the policy keeps. -/
def keepOf : Policy → Peer → Bool
  | .retain => fun _ => true
  | .revoke S => fun q => !S q

/-- pol_retain and pol_revoke of congruence.py. -/
def out (p : Policy) (s : Hist) : Fin 3 := total (keepOf p) s

/-- Allowed outputs for history `h`, continuation `k` and policy `p`. -/
def allowed (h k : Hist) (p : Policy) (o : Fin 3) : Prop := o = out p (h ++ k)

/-- Definition 2, enough: one transition reading only `C h` (and the later events)
    yields an allowed output for every history, continuation and policy. -/
def Enough {σ : Type} (C : Hist → σ) : Prop :=
  ∃ f : σ → Hist → Policy → Fin 3, ∀ h k p, allowed h k p (f (C h) k p)

/-- Definition 2, separating pair: equal summaries, disjoint allowed outputs. -/
def Separates {σ : Type} (C : Hist → σ) (h₁ h₂ k : Hist) (p : Policy) : Prop :=
  C h₁ = C h₂ ∧ ∀ o, ¬ (allowed h₁ k p o ∧ allowed h₂ k p o)

/-- A separating pair rules out every transition, so the summary is not enough. -/
theorem not_enough_of_separates {σ : Type} {C : Hist → σ} {h₁ h₂ k p}
    (hs : Separates C h₁ h₂ k p) : ¬ Enough C := by
  intro ⟨f, hf⟩
  have e := hs.1
  exact hs.2 (f (C h₁) k p) ⟨hf h₁ k p, e ▸ hf h₂ k p⟩

/-- The two kinds: the per-peer sums mod 3. -/
def perPeer (h : Hist) : Fin 3 × Fin 3 := (total (· == .A) h, total (· == .B) h)

theorem total_append (keep : Peer → Bool) (h k : Hist) :
    total keep (h ++ k) = total keep h + total keep k := by
  induction h with
  | nil => simp [total]
  | cons e h ih =>
    obtain ⟨p, v⟩ := e
    simp only [List.cons_append, total, ih]
    exact (by decide : ∀ a b c : Fin 3, a + (b + c) = a + b + c) _ _ _

theorem total_split (keep : Peer → Bool) (h : Hist) :
    total keep h = (if keep .A then total (· == .A) h else 0)
                 + (if keep .B then total (· == .B) h else 0) := by
  induction h with
  | nil => cases keep .A <;> cases keep .B <;> rfl
  | cons e h ih =>
    obtain ⟨p, v⟩ := e
    simp only [total, ih]
    cases p <;> cases keep .A <;> cases keep .B <;> simp <;> revert v <;>
      generalize total (· == .A) h = a <;> generalize total (· == .B) h = b <;>
      revert a b <;> decide

/-- The transition: rebuild the policy's sum from the per-peer sums, then add the
    continuation. It never looks at `h` itself. -/
def resume (s : Fin 3 × Fin 3) (k : Hist) (p : Policy) : Fin 3 :=
  (if keepOf p .A then s.1 else 0) + (if keepOf p .B then s.2 else 0) + out p k

/-- Lemma 1 (enough). Per-peer sums mod 3 are enough for retain and every revoke(S),
    for histories and continuations of any length. -/
theorem perPeer_enough : Enough perPeer := by
  refine ⟨resume, fun h k p => ?_⟩
  unfold allowed resume out
  rw [total_append, total_split (keepOf p) h]
  rfl

/-- Lemma 2 (irredundant). Keeping only the total sum is not enough.
    A contributes 1 or B contributes 1, then A leaves under revoke. -/
theorem total_separates :
    Separates (total (fun _ => true)) [(.A, 1)] [(.B, 1)] [] (.revoke (· == .A)) := by
  refine ⟨by decide, fun o ⟨h₁, h₂⟩ => ?_⟩
  simp only [allowed] at h₁ h₂
  exact absurd (h₁.symm.trans h₂) (by decide)

theorem total_not_enough : ¬ Enough (total (fun _ => true)) :=
  not_enough_of_separates total_separates

/-- Each kind alone is needed too. Dropping B's sum keeps only A's sum, and vice versa. -/
theorem dropB_not_enough : ¬ Enough (total (· == .A)) :=
  not_enough_of_separates (h₁ := []) (h₂ := [(.B, 1)]) (k := []) (p := .retain)
    ⟨by decide, fun o ⟨h₁, h₂⟩ => absurd (h₁.symm.trans h₂) (by decide)⟩

theorem dropA_not_enough : ¬ Enough (total (· == .B)) :=
  not_enough_of_separates (h₁ := []) (h₂ := [(.A, 1)]) (k := []) (p := .retain)
    ⟨by decide, fun o ⟨h₁, h₂⟩ => absurd (h₁.symm.trans h₂) (by decide)⟩

/-! Bounded sanity check against congruence.py (L = 3, K = 2, Pi_base). -/

def events : List Event := [.A, .B].flatMap fun p => [0, 1, 2].map (p, ·)

def upTo : Nat → List Hist
  | 0 => [[]]
  | n + 1 => [[]] ++ (upTo n).flatMap fun h => events.map (· :: h)

def subsetsS : List (Peer → Bool) :=
  [fun _ => false, (· == .A), (· == .B), fun _ => true]

/-- gt_classes signature: outputs under every continuation of length ≤ 2 and every policy. -/
def gtSig (h : Hist) : List Nat :=
  (upTo 2).flatMap fun k => (Policy.retain :: subsetsS.map .revoke).map fun p => (out p (h ++ k)).val

def countDistinct {α} [BEq α] (xs : List α) : Nat := (xs.foldl (fun acc x => if acc.contains x then acc else x :: acc) []).length

#eval countDistinct ((upTo 3).map fun h => ((perPeer h).1.val, (perPeer h).2.val))  -- 9
#eval countDistinct ((upTo 3).map gtSig)  -- 9

set_option maxRecDepth 100000 in
theorem perPeer_classes_L3 :
    countDistinct ((upTo 3).map fun h => ((perPeer h).1.val, (perPeer h).2.val)) = 9 := by
  decide

end Lifeline
