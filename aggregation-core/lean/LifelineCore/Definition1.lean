/-
Definition 1 in the abstract, kept apart from the aggregation core.
An input bundles the recorded history and the continuation. The committed output and
the output after the transition are folded into one `Out`.
-/
namespace Lifeline.Def1

/-- Definition 1: the compiled run under change `d` gives an output that `P` allows. -/
def Correct {Input Change Out : Type} (P : Input → Option Change → Out → Prop)
    (compiled : Input → Option Change → Out) (d : Option Change) : Prop :=
  ∀ x, P x d (compiled x d)

/-- Lemma 3. With no change and the policy that allows only the interpreter's output,
    Definition 1 is classical compiler correctness. -/
theorem no_change_is_compiler_correctness {Prog Code Input Change Out : Type}
    (interp : Prog → Input → Out) (compile : Prog → Code) (exec : Code → Input → Out)
    (prog : Prog) :
    Correct (Change := Change) (fun x _ o => o = interp prog x)
        (fun x _ => exec (compile prog) x) none
      ↔ ∀ x, exec (compile prog) x = interp prog x :=
  Iff.rfl

end Lifeline.Def1
