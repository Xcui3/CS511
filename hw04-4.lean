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

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/- # assignment 4 -/

/- 4.a -/
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use (7 * k + 1)
  calc
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw[hk]
    _ = 2 * (7 * k + 1) + 1 := by ring
  

/- 4.b -/
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hx
  obtain ⟨q, hq⟩ := hy
  use (2*k * q + 3*q + k + 1)
  calc
    x * y + 2 * y = (2*k+1) * (2*q+1) + 2 * (2*q+1) := by rw[hk,hq]
    _ = 2*(2*k * q + 3*q + k + 1) + 1 := by ring
  

/- 4.c -/
example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Odd] at *
  dsimp [Even] at *
  obtain ⟨r, hr⟩ := hn
  use (2*r ^2 + 2* r - 3)
  calc
    n ^ 2 + 2 * n - 5 = (r+r)^2 + 2*(r+r) - 5 := by rw [hr]
    _ = 2*(2*r ^2 + 2* r - 3) + 1 := by ring



/- 4.d -/
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ha | ha := Int.even_or_odd a
  obtain hb | hb := Int.even_or_odd b
  left
  dsimp[Int.Even] at *
  obtain  ⟨q, hq⟩ := ha
  obtain  ⟨k, hk⟩ := hb
  dsimp[Even]
  use q - k
  calc 
    a - b = 2*q - 2*k := by rw[hq,hk]
    _ = q- k + (q - k) := by ring
  obtain hc | hc := Int.even_or_odd c
  right
  left
  dsimp[Int.Even] at *
  dsimp[Even] at *
  obtain ⟨q,hq⟩ := ha
  obtain ⟨k,hk⟩ := hc
  use q + k
  calc
    a + c = 2 * q + 2 * k := by rw [hq,hk] 
    _ = q + k + (q + k) := by ring
  
  dsimp[Int.Odd] at *
  right
  right
  dsimp[Even] 
  obtain ⟨q,hq⟩ := hb
  obtain ⟨k,hk⟩ := hc
  use q - k
  calc
    b - c = 2 * q + 1 - (2 * k + 1) := by rw[hq,hk]
    _ = q- k + ( q - k) := by ring

  obtain hb | hb := Int.even_or_odd b
  obtain hc | hc := Int.even_or_odd c
  dsimp[Int.Even] at *
  right
  right
  dsimp[Even] at *
  obtain ⟨q,hq⟩ := hb
  obtain ⟨k,hk⟩ := hc
  use q - k
  calc
    b - c = 2 * q - (2 * k) := by rw[hq,hk]
    _ = q- k + ( q - k) := by ring
  
  right
  left
  dsimp[Int.Odd] at *
  dsimp[Even]
  obtain ⟨q,hq⟩ := ha
  obtain ⟨k,hk⟩ := hc
  use (q + k + 1)
  calc
    a + c = 2 * q + 1  + (2 * k + 1):= by rw[hq,hk]
    _ = q + k + 1 + (q + k + 1) := by ring

  left
  dsimp[Int.Odd] at *
  dsimp[Even]
  obtain ⟨q,hq⟩ := ha
  obtain ⟨k,hk⟩ := hb
  use q - k
  calc
    a -b = 2*q + 1 - (2 * k + 1) := by rw [hq , hk]
    _ = q - k + (q - k) := by ring
