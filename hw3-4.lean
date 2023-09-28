import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

/- # assignment 3 -/

/- 4.a -/ 
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  . have hxt' : 0 < - x * t := by addarith [hxt]
    have htemp: -x * t = x * (-t) := by ring
    have hxt2: 0 <  x*(-t) := by 
      calc
        0 < -x * t := by addarith [hxt]
        _ = x * (-t) := by rel [htemp]
    cancel x at hxt2  
    have h : t < 0 := by addarith[hxt2]
    apply ne_of_lt
    apply h

/- 4.b -/

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use (a+1)
  use a
  calc
    (a+1)^2 - a^2 = 2*a + 1 := by ring



/- 4.c -/

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p+q)/2
  constructor
  . have h1 : p + p < p + q := by addarith [h] 
    have h2 : 2*p  = p + p := by ring
    calc 
        p = (p+p)/2 := by ring
        _ < (p+q)/2 := by rel[h1]

  . have h1 : p + q < q+q := by addarith [h]
    have h2 : q + q = 2*q := by ring
    calc 
      q = (q+q)/2 := by ring
      _ > (p+q) /2 := by rel[h1]

