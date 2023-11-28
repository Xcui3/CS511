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
def Bijective (f : X → Y) : Prop := Injective f ∧ Surjective f
/- # assignment 11 -/

/- 5.a -/
example : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
    dsimp[Bijective]
    constructor
    . dsimp [Injective]
      intro x1 x2 hx
      ring
      have h1: -3* x1 = -3* x2:= by
        calc
          -3 *x1 = 4 - 3*x1 - 4 := by ring
          _ = 4 - 3*x2 - 4 := by rw[hx]
          _ = -3*x2 := by ring
      cancel -3 at h1
    . dsimp [Surjective]
      intro y
      use (y - 4) / -3
      ring

/- 5.b -/



example : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  dsimp [Bijective]
  push_neg
  intro h1 h2
  dsimp [Surjective] at *
  have h3:= h2 (-10)
  obtain ⟨x,hx⟩ := h3

  have h4: x^2 + 2*x + 1 ≥ 0 := by
    calc
      x^2 + 2*x + 1 = (x + 1)^ 2 := by ring
      _ ≥ 0 := by extra
  have h5: x^2 + 2*x > -10 := by
    calc
      x^2 + 2*x = x^2 + 2*x + 1 - 1 := by ring
      _ ≥ 0 -1 := by rel[h4]
      _ = -1 := by numbers
      _ > -10 := by numbers

  have h6: -10 < -10 := by
    calc
      -10 < x^2 + 2 * x := by rel[h5]
      _ = -10 := by rw[hx]

  contradiction



/- 5.c -/
def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := sorry
def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id
example : Inverse u v := by
  dsimp [Inverse]
  sorry
/- 5.d -/
example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  sorry
