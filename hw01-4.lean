import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

example {a b : ℤ} (h1 : a = 2*b + 5) (h2 : b = 3) : a = 11 := 
  calc 
    a = 2*3 + 5 by rw [h1, h2] 
    _ = 11 := by ring

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := 
  calc 
    x = -2 := by ring

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := 
  calc
    (h3 : b = 1) := by ring 
    (h4: a = 5*b + 4) := by ring 
    _ = 5 * 1 + 4 := by rw [h4, h3 ]  
    _ = 9 by ring 

