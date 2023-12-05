import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Library.Theory.InjectiveSurjective
import Mathlib.Tactic.Set
import Library.Tactic.ExistsDelaborator
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Mathlib.Tactic.GCongr
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use
import Library.Tactic.Product

set_option push_neg.use_distrib true
open Function

/- 3 points -/
theorem problem4a {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
    dsimp [Surjective] at *
    intro y
    have h1:= hg y
    obtain ⟨ x,h2 ⟩ := h1
    have h3 := hf x
    obtain ⟨ x1, hx1⟩ := h3
    use x1
    calc
      g (f x1) = g x := by rw[hx1]
      _ = y := by rw[h2]

/- 2 points -/
theorem problem4b {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  dsimp [Surjective] at *
  choose g hg using hf
  use g
  ext x
  have h1 := hg x
  calc
    (f ∘ g) x = f ( g  x) := by rfl
    _ = x := by  rw [h1]
    _ = id x := by rfl

/- 2 points -/
theorem problem4c {f : X → Y} {g : Y → X} (h : Inverse f g) : Inverse g f := by
  dsimp [Inverse] at *
  constructor
  . obtain ⟨ h1,h2 ⟩ := h
    apply h2
  . obtain ⟨ h1,h2 ⟩ := h
    apply h1

/- 3 points -/
theorem problem4d {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by

    dsimp [Inverse] at *
    obtain ⟨h3,h4⟩ := h1
    obtain ⟨h5,h6⟩ := h2

    ext x
    have h7 : g1 ( f (g2 x)) = id ( g2 x) := by -- this should be easy by rfl but strangely it doesn't work
      sorry
    calc
      g1 x = g1 (id x) := by rfl
      _ = g1 ( (f ∘ g2) x) := by rw[h6]
      _ = g1 (f (g2 x)) := by rfl
      _ = id (g2 x) := by rw[h7]
      _ = g2 x := by rfl


/- 1 points -/
theorem problem5a1 : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Injective]
  push_neg
  use (0, 0), (2, 1)
  constructor
  . numbers
  . numbers


/- 1 points -/
theorem problem5a2 : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  push_neg
  dsimp [Surjective]
  intro b
  use (b+1 , 0)
  numbers
  ring

/- 2 points -/
theorem problem5b : ¬ Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 + y ^ 2) := by
  push_neg
  dsimp [Surjective]
  intro h1
  have h2 := h1 (-1)
  obtain ⟨ a , ha ⟩ := h2
  have h2: a.fst ^2 + a.snd ^2 ≥  0 := by extra
  have h3: a.fst ^2 + a.snd ^2 > -1 := by
    calc
      a.fst ^2 + a.snd ^2 ≥ 0 := by rel [h2]
      _ > -1 := by addarith
  have h4: -1 > -1 := by sorry -- should be easy by h2 and h3 but here it gives error

  contradiction



/- 3 points -/
theorem problem5c : ¬ Injective
    (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by

  dsimp [Injective]
  push_neg
  use (0, 0, 0), (1, -2 , 1)
  constructor
  . numbers
  . numbers

/- 3 points -/
theorem problem5d : Injective (fun ((x, y) : ℝ × ℝ) ↦ (x + y, x + 2 * y, x + 3 * y)) := by
  intro (x1, y1) (x2, y2) h
  dsimp at h
  obtain ⟨h, h', hy⟩ := h
  have h1: y1 + y2 = 2*y1 := by
    calc
      y1 + y2 = x1 + y1 - x1 + y2:= by ring
      _ = x2 + y2 - x1 +y2:= by rw[h]
      _ = x2 + 2*y2 - x1 := by ring
      _ = x1 + 2*y1  - x1 := by rw[h']
      _ = 2*y1 := by ring
  have h2: y2 = y1 := by
    calc
      y2 = y1 + y2 - y1 := by ring
      _ = 2*y1 - y1 := by rw[h1]
      _ = y1 := by ring
  constructor
  . calc
      x1 = x1 + y1 - y1 := by ring
      _ = x2 + y2 - y1 := by rw[h]
      _ = x2 + y1 - y1 := by rw[h2]
      _ = x2 := by ring
  . tauto
