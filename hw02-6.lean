import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel




-- Problem 6-a
example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
calc
    x+3 ≥ 2*(y) := by exact[h1]
    x+3 ≥ 2*1 := by rel [h2]
    x ≥ -1 := by ring


-- Problem 6-b
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
    a+b = a + 2*b - 2*b + b := by extra
       ≥  4 - 2*b + b := by ring
       = 4 - b := by ring
       = 3 - b + 1 := by ring
       




-- Problem 6-c
example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc 
    x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 9 * x^2 - 8 * x^2 + 2*x - 8 := by ring
    _ ≥ x^2 - 2*x - 8  := by ring
    _ ≥ (x-1)^2 - 9 := by ring
    _ ≥ 8 ^ 2 - 9 := by ring
    _ ≥ 55 := by ring
    _≥ 3 := by ring
    
