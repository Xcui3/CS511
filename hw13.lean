import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Set
import Library.Theory.Comparison
import Library.Theory.InjectiveSurjective
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Define
import Library.Tactic.ExistsDelaborator
import Library.Tactic.Extra
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Product
import Library.Tactic.Rel
import Library.Tactic.Use


set_option push_neg.use_distrib true
open Set

notation:50 a:50 " ⊈ " b:50 => ¬ (a ⊆ b)

/- 3 points -/
theorem problem4a : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  dsimp [Set.subset_def]
  push_neg
  use 5
  constructor
  . tauto
  . intro h
    obtain ⟨a, ha⟩ := h
    have h1:= le_or_succ_le a 0
    obtain h1 | h1 := h1
    . have h2 :=
        calc
          20 * a ≤ 20 * 0 := by rel [h1]
          _ = 0 := by numbers
          _ < 5 := by addarith
      have h3 :=
        calc
          5 = 20 * a := by rw[ha]
          _ < 5 := by rel [h2]
      contradiction

    . have h2 :=
        calc
          20 * a ≥ 20 * 1 := by rel[h1]
          _ = 20 := by numbers
          _ > 5 := by addarith
      have h3 :=
        calc
          5 = 20 * a := by rw[ha]
          _ > 5 := by rel[h2]
      contradiction

/- 3 points -/
theorem problem4b : {k : ℤ | 7 ∣ 9 * k} = {l : ℤ | 7 ∣ l} := by
  ext n
  dsimp
  constructor
  · intro hn
    obtain ⟨k, hk⟩ := hn
    use 4*k - 5*n
    calc
      n = 4* (9 * n) - 7 * 5 * n := by ring
      _ = 4 * (7 * k) - 7*5 * n := by rw[hk]
      _ = 7 * (4*k - 5 * n) := by ring
  . intro h
    obtain ⟨k, hk⟩ := h
    use 9 * k
    calc
      9 * n = 9 * ( 7 * k) := by rw[hk]
      _ = 7 * (9 * k) := by ring

/- 4 points -/
theorem problem4c : {x : ℝ | x ^ 2 + 3 * x + 2 = 0} = {-1, -2} := by
  ext x
  dsimp
  constructor
  · intro h
    have h1 :=
      calc
        (x+1)* (x+2) = x^2 + 3*x + 2 := by ring
        _ = 0 := by rw[h]
    rw [mul_eq_zero] at h1
    obtain h1 | h1 := h1
    . left
      addarith [h1]
    . right
      addarith [h1]
  . intro h
    obtain h | h := h
    . calc
        x ^ 2 + 3 * x + 2 = (-1) ^ 2 + 3 * (-1) + 2 := by rw[h]
        _ = 0 := by numbers
    . calc
        x ^ 2 + 3 * x + 2 = (-2) ^ 2 + 3 * (-2) + 2 := by rw[h]
        _ = 0 := by numbers

/- 3 points -/
theorem problem5a : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp [Set.subset_def]
  intro n h
  obtain ⟨h1, h2⟩ := h
  constructor
  . use 5 * h1 + 3
    calc
      n - 1 = n - 7 + 6 := by ring
      _ = 10 * h1 + 6 := by rw[h2]
      _ = 2 * (5 * h1 + 3) := by ring
  . use 2*h1 + 1
    calc
      n-2 = n-7 + 5 := by ring
      _ = 10 * h1 + 5 := by rw[h2]
      _ = 5 * (2 * h1 + 1) := by ring

/- 3 points -/
theorem problem5b : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  dsimp [Set.subset_def]
  intro n h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨k,hk⟩ := h1
  rw [hk] at h2
  obtain ⟨q, hq⟩ := h2
  have h3:=
    calc
      k = 25 * k  - 24 * k := by ring
      _ = 5 * ( 5 * k) - 8 * (3 * k) := by ring
      _ = 5 * ( 8 * q) - 8 * (3 * k) := by rw[hq]
      _ = 8 * (5 *q - 3 * k) := by ring
  rw [h3] at hk
  use 5 * q - 3 * k
  calc
    n = 5 * (8 * ( 5 * q - 3 * k) ) := by rw [hk]
    _ = 40 * (5 * q - 3 * k) := by ring

/- 4 points -/
theorem problem5c :
    {n : ℤ | 3 ∣ n} ∪ {n : ℤ | 2 ∣ n} ⊆ {n : ℤ | n ^ 2 ≡ 1 [ZMOD 6]}ᶜ := by
  dsimp [Set.subset_def]
  intro n h
  obtain h | h := h
  . intro h2
    obtain ⟨q,hq⟩ := h2
    obtain ⟨k , hk⟩ := h
    have h1:=
      calc
        n ^ 2 - 1 = (3 * k) ^ 2 -1 := by rw[hk]
        _ = 9 * k ^ 2 - 1 := by ring
    sorry
  . intro h2
    obtain ⟨q,hq⟩ := h2
    sorry
