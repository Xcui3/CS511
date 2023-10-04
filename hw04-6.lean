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

/- # assignment 4 -/

/- 6.a -/
example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  have H: x^2 +x - 6 = (x+3) * (x-2) := by ring
  constructor
  . intro h
    have h1: (x + 3) * (x - 2) = 0 := by 
      calc
        (x + 3) * (x - 2) = x ^ 2 + x - 6 := by rw[H]
        _ = 0 := by apply h
    have h2:= eq_zero_or_eq_zero_of_mul_eq_zero h1
    obtain h3 | h4 := h2
    . left
      calc
        x = (x+ 3 ) -3 := by ring
        _ = -3 := by addarith[h3]
    . right
      calc 
        x = (x- 2) + 2 := by ring
        _ = 2  := by addarith[h4]
  . intro h
    obtain h3 | h4 := h 
    . calc
      x^2 + x - 6 = (-3)^2 + (-3) - 6 := by rw[h3]
      _ = 0 := by ring
    . calc
      x^2 + x - 6 = (2)^2 + (2) - 6 := by rw[h4]
      _ = 0 := by ring
  
example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


/- 6.b -/
example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  intro h
  have H: (2*a - 5)^2 ≤ 1^2 := by
      calc
        (2*a - 5)^2 = 4*(a^2 -5 * a + 5) + 5 := by ring
        _ ≤ 4* (-1) + 5  := by rel[h]
        _ = 1^2 := by ring 
    
  have h2:  -1 ≤ (2*a-5) ∧ (2*a-5) ≤ 1  := by 
    apply abs_le_of_sq_le_sq' H
    numbers
  obtain ⟨h3,h4⟩ := h2 
  
  have h5 : 2*a ≤ 2 * 3 := by addarith[h4]
  have h6 : a ≤ 3 := by cancel 2 at h5
  
  have h7 : 2 * a ≥ 2 * 2 := by addarith[h3]
  have h8 : a ≥ 2 := by cancel 2 at h7 
  have hh6 : a ≤ 2 ∨ a ≥ 3 := by apply le_or_succ_le a 2 
  obtain hh7 | hh8 := hh6
  left
  . apply le_antisymm
    . exact hh7
    . exact h8
  right
  . apply le_antisymm
    . exact h6
    . exact hh8

  intro h
  obtain h1|h2 := h
  . calc
      a ^ 2 - 5 * a + 5 = 2 ^ 2 - 5 * 2 + 5 := by rw[h1]
      _ = -1 := by ring
      _ ≤ -1 := by numbers
  . calc
      a ^ 2 - 5 * a + 5 = 3^2 - 5*3 + 5 := by rw[h2]
      _ = -1 := by ring
      _ ≤ -1 := by numbers

    
    

    
    









