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
import Library.Tactic.Induction
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.GCongr

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

/- # assignment 9 -/

/- 4.a -/
def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

example (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with n IH
  . -- base case
    numbers
    simp
  . -- inductive step
    calc
      B (n + 1) = B n + (n + 1 : ℚ) ^ 2 :=by rw [B]
      _ = (n: ℚ) * (n + 1 : ℚ) *(2 * n+ 1 : ℚ) /6 + (n+1 : ℚ)^2 := by rw[IH]
      _ = ((n: ℚ) * (n + 1 : ℚ) *(2 * n+ 1 : ℚ) + 6* (n+1 : ℚ)^2 ) / 6 := by ring
      _ = (((n:ℚ) * (2*n + 1: ℚ) + 6*(n+1 :ℚ)) *(n + 1 :ℚ)) / 6 := by ring
      _ = ((2 * (n:ℚ ) ^ 2 + 7*n + 6 : ℚ)*(n+1 :ℚ))/6 := by ring
      _ = ((2*n+3 : ℚ) * (n+2) *(n+1 :ℚ))/6 := by ring
      _ = (↑n + 1) * (↑n + 1 + 1) * (2 * (↑n + 1) + 1) / 6 := by ring

/- 4.b -/
def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

lemma sum_S_n (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with n IH
  . -- base case
    numbers
    simp
  . -- inductive step
    calc
      S (n + 1) = S n + 1 / 2 ^ (n + 1) := by rw[S]
      _ = 2 - 1 / 2 ^ n +  1 / 2 ^ (n + 1) := by rw [IH]
      _ = 2 - 1 / 2 ^ (n + 1) := by ring

/- 4.c -/
example (n:ℕ ) : S n ≤ 2 := by
  have h1: (1 / 2 ^ n :ℚ) > 0 := by
      extra
  calc
    S n = 2 - 1 / 2 ^ n  := by rw[sum_S_n]
    _ ≤ 2 := by addarith[h1]
/- 4.d -/
lemma geq_base_geq (n k :ℕ ) : (k + 1) ^ n ≥ k ^ n := by
      simple_induction n with n IH2
      . -- base case
        numbers
        simp
      . --inductive step
        calc
          (k + 1) ^ (n + 1) = (k + 1) ^ n * (k + 1) := by ring
          _ ≥ k ^ n * ( k + 1) := by rel[IH2]
          _ = k ^ ( n +1) + k ^ n := by ring
          _ ≥ k ^ (n+1) := by extra

example (n : ℕ) : (n + 1)! ≤  (n + 1) ^ n := by
  simple_induction n with n IH
  . -- base case
    numbers
    simp
  . -- inductive step
    have h1 : (n+2) ^ n ≥ (n+1) ^ n := by
      apply geq_base_geq
    calc
      (n + 1 + 1)! = (n+2) * (n + 1)! := by rw[factorial]
      _ ≤ (n+2) * (n+1) ^ n := by rel[IH]
      _ ≤ (n+2) * (n+2) ^ n := by rel[h1]
      _ = (n + 1 + 1)^ (n+1) := by ring
