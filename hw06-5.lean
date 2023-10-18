import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use
attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/- # assignment 6 -/

/- 5.a -/
def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  use 1
  dsimp [Tribalanced]
  constructor
  . intro n
    have h1 : n ≤ 0 ∨ n ≥ 1 := by apply le_or_succ_le n 0
    obtain h2|h3 := h1
    . have h3 : n= 0 := by addarith [h2] 
      sorry

    . sorry
  . conv => ring_nf
    intro h 
    have h1:= h 1
    have h2: 3 < 3 := by sorry
    contradiction
  

/- 5.b -/
def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)
example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1
  constructor
  . dsimp [Superpowered]
    intro n 
    conv => ring_nf 
    apply prime_two
  . conv => ring_nf
    dsimp [Superpowered]
    intro h 
    have h1:= h 5
    conv at h1 => ring_nf
    dsimp [Prime] at h1 
    obtain ⟨h2,h3⟩ := h1
    have h4:= h3 641
    have h5: 641 = 1 ∨ 641 = 4294967297 := by 
      apply h4
      use 6700417
      ring 
    obtain h6 | h7 := h5
    . contradiction
    . contradiction
 