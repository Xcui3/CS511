import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use
import Mathlib.Data.Nat.Basic
attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/- # assignment 3 -/

/- 5.a -/

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have hn := le_or_gt x 1
  obtain h1 | h2 := hn
  . use 2
    have h3: 4 > x:= by addarith[h1]
    calc
      2^2 = 4 := by numbers
      _ > x := by rel[h3]
  . use x
    have h3: x*x > x*1 := by rel[h2,h2]
    calc
      x^2 = x * x := by ring
      _ > x * 1 := by rel[h3]
      _ = x     := by ring



/- 5.b -/
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, ha⟩ := h
  have h1: a*t-a < t-1 := by addarith[ha]
  have h2: a*(t-1) = a*t - a := by ring
  have h3: a*(t-1) < t-1 := by 
    calc 
        a*(t-1) = a*t - a := by exact h2
        _ < t - 1  := by rel [h1]
  have ht := le_or_gt t 1
  obtain ht1 | ht2 := ht
  . intro H
    have h4 := by 
      calc
        a *(t-1) = a*(1-1) := by rw[H]
        _ = 0  := by ring
    have h5 := by 
      calc
        t - 1 > a * (t-1) := by exact h3
        _ = 0 := by rw[h4]
    have h6 : t> 1 := by addarith[h5]
    have h7 := by 
      calc
        1 = t  := by addarith[H]
        _ > 1 := by rel [h6]

    have h8 : False :=by numbers at h7
    apply h8
  . apply ne_of_gt
    have hf:  1 < t := by addarith[ht2]
    apply hf

    


/- 5.c -/
example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨t, ht⟩ := h
  have hn := le_or_lt t 2
  obtain h1 | h2 := hn
  . have h2 : 2*t ≤ 2*2 := by rel[h1]
    have h3 : m = 2 * t := by addarith[ht]
    have h4 : m ≤ 2*t := by extra
    have h5 : m ≤ 2*2 := by addarith[h2,h4]
    apply ne_of_lt
    calc
      m ≤ 2*2 := by addarith[h5]
      _ = 4  := by numbers
      _ < 5  := by addarith

  . have h3 : 3 ≤  t := by addarith[h2] 
    have h4 : 2*3 ≤ 2*t := by rel[h3,h3]
    have h5 : 2*t ≥ 2*3 := by addarith[h4]
    have h6 : m ≥ 2*t := by extra
    have h7 : m ≥ 2*3 := by addarith[h6,h5]
    apply ne_of_gt
    calc
      m ≥ 2*3 := by addarith[h7]
      _ = 6  := by numbers
      _ > 5  := by addarith


