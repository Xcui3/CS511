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
import Mathlib.Data.Nat.Basic
notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/- # assignment 4 -/

/- 5.a -/
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have H: (a+b)/2≥ a ∨ (a+b)/2 ≤ b := by apply h
  obtain h1 | h2 := H
  calc
    b = 2* ((a+b)/2) - a := by ring
    _ ≥ 2 * a - a := by rel[h1]
     _ = a  := by ring

  calc
    a = 2 * ((a+b)/2) - b := by ring
     _ ≤ 2 * b - b := by rel[h2]
      _ = b := by ring


/- 5.b -/
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x
  intro y
  intro h
  have h1 : (x + y)^2 ≤ 3^2 := by
    calc
      (x + y)^2  ≤  (x+y)^ 2 + (x-y)^2 := by extra
      _ = 2 * (x^2 + y^2)  := by ring
      _ ≤ 2 * (4) := by rel[h]
      _ ≤ 3 ^ 2  := by numbers
  have h2 : -3 ≤ x + y ∧ x + y ≤ 3 := by
     apply abs_le_of_sq_le_sq' h1
     extra
  obtain ⟨h3,h4⟩ := h2
  addarith[h3]


/- 5.c -/
example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  have h1: 1 ≤ 3 → 3 ≤ 5 → 3 ∣ n := hn 3
  have h2: 1 ≤ 5 → 5 ≤ 5 → 5 ∣ n := hn 5
  
  have h3: 3 ∣ n := by 
    apply h1
    numbers
    numbers
  have h4: 5 ∣ n := by
    apply h2
    numbers
    numbers
  obtain ⟨k,hk⟩ := h3
  obtain ⟨q,hq⟩ := h4
  use 2*q - k
  calc
    n = 6 * n - 5 * n  := by ring
    _ = 6 * (5 * q) - 5* n  := by rw[hq]
    _ = 6 * (5 * q) - 5* (3 * k) := by rw[hk]
    _ = 15 * (2*q - k)  := by ring


/- 5.d -/
example : forall_sufficiently_large x: ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  dsimp
  use 7
  intro n hn
  calc
    n ^ 3 + 3 * n = n * n^2 + 3*n := by ring
    _ ≥ 7 * n^2 + 3 * 7  := by rel[hn]
    _ = 7 * n^2 + 21 := by ring
    _ = 7 * n^2 + 12 + 9 := by ring 
    _ ≥ 7 * n^2 + 12 := by extra 





 