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

/- 4.a -/
example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  . intro hn
    obtain ⟨k,hk⟩ := hn
    constructor
    . use (9*k)
      calc 
        n = 63 * k := by rw[hk]
        _ = 7 * (9 * k) := by ring
    . use (7*k)
      calc 
        n = 63 * k := by rw[hk]
        _ = 9 *(7*k) := by ring
  . intro hn
    obtain ⟨hk,hq⟩ := hn
    obtain ⟨k,h7⟩ := hk
    have hqq : 9 ∣ 7*k := by 
      calc
          9 ∣ n  := by exact hq
          _  ∣ 7*k := by rw [h7]

    obtain ⟨q,hkq⟩ := hqq 
    have h1 : 9 ∣ k := by
      use (4*q - 3* k)
      calc
        k = 28 * k - 27 * k := by ring
        _ = 4* (7 * k) - 27 * k  := by ring
        _ = 4 * (9 * q) - 27 * k := by rw[hkq]
        _ = 9 * (4 * q - 3 * k) := by ring
    obtain ⟨x,h2⟩ := h1
    use x
    calc
      n = 7 * k := by exact h7
      _ = 7 * (9 * x) := by rw[h2]
      _ = 63 * x := by ring
  


/- 4.b -/
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor 
  . intro h1
    have h2 : k^2 ≤ 4 ∨ k^2 ≥ 5 := by apply le_or_succ_le (k^2) 4
    obtain h3 | h4 := h2
    . have h3 : k^2 ≤ 2^2 := by
        calc 
          k^2 ≤ 4 := by extra 
          _ = 2^2 := by numbers 

      
      /-have h4 : (- 2) ≤ k ∧ k ≤ 2 := by
        apply abs_le_of_sq_le_sq' h3 
        extra     
      -/
      sorry
  . intro h1
    obtain h2 | h3 := h1
    calc
      k ^ 2 = 0 ^ 2 := by rw[h2]
      _ = 0 := by numbers
      _ ≤ 6 := by numbers
    obtain h4 | h5 := h3
    calc 
       k ^ 2 = 1 ^ 2 := by rw[h4]
      _ = 1 := by numbers
      _ ≤ 6 := by numbers
    calc
      k ^ 2 = 2 ^ 2 := by rw[h5]
      _ = 4 := by numbers
      _ ≤ 6 := by numbers

