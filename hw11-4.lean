import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Mathlib.Tactic.Set
import Library.Tactic.ExistsDelaborator
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Mathlib.Tactic.GCongr
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

def Injective (f : X → Y) : Prop := ∀ {x1 x2 : X}, f x1 = f x2 → x1 = x2
def Surjective (f : X → Y) : Prop := ∀ y : Y, ∃ x : X, f x = y
/- # assignment 11 -/

/- 4.a -/

example : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  dsimp[Surjective]
  push_neg
  use (fun x : ℤ ↦ x)
  constructor
  . intro y
    use y
    simp
  . use 1
    intro
    simp
    push_neg
    sorry



/- 4.b -/
example : ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  dsimp[Surjective]
  intro y c
  use c / y
  calc
    y * (c / y) = y * c / y := by ring
    _ = c * y / y := by ring
    _ = c := by sorry

/- 4.c -/
/- lemma lt_trichotomy (x y : ℚ) : x < y ∨ x = y ∨ x < y := -/
example {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
    dsimp[Injective]
    intro x1 x2
    intro
    have h1: lt_trichotomy x1 x2
    sorry


/- 4.d -/
example {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  dsimp [Surjective]
  intro y
  sorry
