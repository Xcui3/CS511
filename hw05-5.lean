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

/- # assignment 5 -/

/- 5.a -/
example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  intro a
  intro h1
  intro h2 
  
  have h5 : (a - 2) ^ 2 ≤ 1^2 := by 
    apply sq_le_sq'
    calc
      -1 = 1 - 2 := by numbers
      _ ≤ a - 2 := by rel[h1]
    
    calc
      a - 2 =  a + (-2) := by ring 
      _ ≤ 3 + (-2) := by rel[h2] 
      _ = 1 := by numbers
  
  calc
    (a - 2) ^ 2 ≤ 1^2 := by exact h5
      _ = 1 := by numbers

  intro y
  intro h1 
  have ha1 := h1 1
  have ha11 : (1 - y) ^ 2 ≤ 1 := by
    apply ha1
    numbers
    numbers

  have ha3 := h1 3
  have ha31: (3 - y) ^ 2 ≤ 1 := by
    apply ha3
    numbers
    numbers

  have h2 : (y - 2) ^ 2 ≤ 0^2 := by
    calc 
      (y - 2) ^ 2 = ((1-y)^ 2 + (3 -y)^2  - 2) / 2 := by ring
      _ ≤ (1 + 1 - 2) / 2 := by rel[ha11,ha31]
      _ = 0 := by numbers
      _ = 0 ^ 2 := by numbers
  
  apply ge_antisymm
  . have h4 :  -0 ≤ y - 2 ∧ y - 2 ≤ 0 := by
      apply abs_le_of_sq_le_sq' h2
      numbers
    obtain ⟨h5,h6⟩ := h4 
    calc
      2 = -0 + 2 := by numbers
      _ ≤ y - 2 + 2 := by rel[h5]
      _ = y := by addarith
  . have h4 :  -0 ≤ y - 2 ∧ y - 2 ≤ 0 := by
      apply abs_le_of_sq_le_sq' h2
      numbers
    obtain ⟨h5,h6⟩ := h4 
    calc
      y = y - 2 + 2 := by ring
      _ ≤ 0 + 2 := by rel[h6]
      _ = 2 := by addarith



/- 5.b -/
example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  numbers 

  intro x
  intro h1
  calc
    x = (4 * x) / 4 := by ring 
    _ = (4 * x - 3 + 3) / 4 := by ring 
    _ = (9 + 3) / 4 := by rw[h1]
    _ = 3 := by numbers 


/- 5.c -/
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor

  . intro x
    extra       

  . intro x 
    intro h1
    have h2 := h1 0
    apply ge_antisymm
    extra
    exact h2



    



  