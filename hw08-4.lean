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
notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/- # assignment 8 -/

/- 4.a -/
example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  . ring
    extra
  . calc
      a ^ (k + 1) = a * (a ^ k):= by ring
      _ ≡ a * (b ^ k) [ZMOD d] := by rel [IH]
      _ ≡ b * (b ^ k) [ZMOD d] := by rel [h]
      _ = b ^ (k+1) := by ring


/- 4.b -/
example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    ring
  · -- inductive step
    have h : k^2 ≥ 2*k + 1:= by
      induction_from_starting_point k, hk with k hk IH2
      . -- base case
        numbers
      . -- inductive case
        calc
          (k + 1)^2 = k^2 + 2*k + 1 := by ring
          _ ≥ 4 ^2 + 2 * k + 1 := by rel [hk]
          _ = 2*k + 17 := by ring
          _ ≥ 2* k  + 3 := by addarith
          _ = 2*(k+1) + 1 := by ring
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 2 := by rel [IH]
      _ = k^2 + k^2 := by ring
      _ ≥ k^2 + (2*k + 1) := by rel [h]
      _ = (k + 1) ^ 2 := by ring

/- 4.c -/
example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k IH
  · -- base case
    ring
    numbers
  · -- inductive step
    have h1: k*a*a ≥ 0 := by
      calc
        k * a * a = k * a^2 := by ring
        _ ≥ 0 := by extra
    have h2: 1+a ≥ 0 := by
      calc
        1+a ≥ 1+ (-1) := by rel[ha]
        _ = 0 := by ring
    calc
      (1 + a) ^ (k + 1) = (1+a) * ((1+a) ^ k) := by ring
      _ ≥ (1+a) * (1 + k * a) := by rel[IH]
      _ = 1 + k * a + a + k * a * a := by ring
      _ ≥ 1 + k * a + a := by extra
      _ = 1 + (k + 1) * a := by ring


/- 4.d -/
example : forall_sufficiently_large n : ℕ, 3 ^ n ≥ 2 ^ n + 100:= by
  dsimp
  use 8
  intro x hx
  induction_from_starting_point x, hx with k hk IH
  . -- base case
    numbers
  . -- inductive case
    calc
      3 ^ (k + 1) = 3 * (3 ^ k) := by ring
      _ ≥ 3 * ((2 ^ k) + 100) := by rel[IH]
      _ = 2 ^ (k + 1) + 2 ^ k + 300 := by ring
      _ ≥ 2 ^ (k + 1) + 300 := by extra
      _ ≥ 2 ^ (k + 1) + 100 := by addarith
