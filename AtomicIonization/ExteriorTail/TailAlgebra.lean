import Mathlib

/-!
# Absorption algebra for the shell estimate
-/

namespace AtomicIonization.ExteriorTail

theorem sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  · nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- The shell constant. -/
noncomputable def tailConstant (c CE L CA D : ℝ) : ℝ :=
  (2 / c) * (3 / 2 + 3 * CE ^ 2 / c) * L ^ 2 * Real.sqrt CA * (1 + Real.sqrt D)

/-- The shell threshold. -/
noncomputable def tailRadius (c CE D : ℝ) : ℝ := max 1 ((16 * CE * (1 + Real.sqrt D) / c) ^ 2)

theorem tailConstant_nonneg {c CE L CA D : ℝ} (hc : 0 < c) : 0 ≤ tailConstant c CE L CA D := by
  unfold tailConstant
  have : 0 ≤ 3 / 2 + 3 * CE ^ 2 / c := by positivity
  positivity

theorem tail_algebra {c CE L CA D r m N G : ℝ} (hc : 0 < c) (hCE : 0 ≤ CE) (hD : 0 ≤ D)
    (hr : tailRadius c CE D ≤ r) (hm : 0 < m) (hG0 : 0 ≤ G)
    (hG : G ≤ 3 / 2 * (L / r) ^ 2 * N) (hN : N ≤ Real.sqrt CA * (1 + Real.sqrt D) * Real.sqrt r)
    (hmain : c * m ≤ 3 / 2 * (L / r) ^ 2 * N +
      2 * m * CE * (1 + Real.sqrt (D * r) + Real.sqrt (G * r / (2 * m))) / r) :
    m ≤ tailConstant c CE L CA D / r := by
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 < r := by linarith
  have hsr : 1 ≤ Real.sqrt r := by rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hr1
  have hsr2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
  have hsD := Real.sqrt_nonneg D
  -- step (i): the inner screened term is absorbed
  have hbig : 16 * CE * (1 + Real.sqrt D) / c ≤ Real.sqrt r := by
    have h := (le_max_right _ _).trans hr
    have h' := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq (by positivity)] at h'
  have hDr : Real.sqrt (D * r) = Real.sqrt D * Real.sqrt r := Real.sqrt_mul hD r
  have hi : 2 * m * CE * (1 + Real.sqrt (D * r)) / r ≤ c / 4 * m := by
    rw [div_le_iff₀ hr0, hDr]
    have h1 : 1 + Real.sqrt D * Real.sqrt r ≤ (1 + Real.sqrt D) * Real.sqrt r := by nlinarith
    have h2 : 16 * CE * (1 + Real.sqrt D) ≤ c * Real.sqrt r := by
      rw [div_le_iff₀ hc] at hbig; linarith
    have h3 : CE * (1 + Real.sqrt D * Real.sqrt r) ≤ CE * ((1 + Real.sqrt D) * Real.sqrt r) :=
      mul_le_mul_of_nonneg_left h1 hCE
    have h4 : CE * ((1 + Real.sqrt D) * Real.sqrt r) ≤ c * r / 16 := by
      have := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg r)
      nlinarith
    have h5 : 2 * m * CE * (1 + Real.sqrt D * Real.sqrt r) ≤ 2 * m * (c * r / 16) := by
      have := h3.trans h4
      have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 2 * m)
      linarith
    have h6 : 0 ≤ m * c * r := by positivity
    have h7 : c / 4 * m * r = 2 * m * (c * r / 16) + m * c * r / 8 := by ring
    linarith
  -- step (ii): the bias cost by AM-GM
  set s := Real.sqrt (G * r / (2 * m)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = G * r / (2 * m) := Real.sq_sqrt (by positivity)
  have hii : 2 * m * CE * s / r ≤ c / 4 * m + 2 * CE ^ 2 * G / (c * r) := by
    have hG' : G = 2 * m * s ^ 2 / r := by rw [hs2]; field_simp
    rw [hG']
    set t := CE * s / r
    have ht : 2 * m * CE * s / r = 2 * m * t := by simp only [t]; ring
    have ht2 : 2 * CE ^ 2 * (2 * m * s ^ 2 / r) / (c * r) = 4 * m * t ^ 2 / c := by
      simp only [t]; field_simp; ring
    rw [ht, ht2]
    have key : 0 ≤ m * (c / 2 - 2 * t) ^ 2 / c := by positivity
    have : m * (c / 2 - 2 * t) ^ 2 / c = c / 4 * m - 2 * m * t + 4 * m * t ^ 2 / c := by
      field_simp; ring
    linarith
  -- combine
  have hsplit : 2 * m * CE * (1 + Real.sqrt (D * r) + s) / r =
      2 * m * CE * (1 + Real.sqrt (D * r)) / r + 2 * m * CE * s / r := by ring
  rw [hsplit] at hmain
  have hGr : 2 * CE ^ 2 * G / (c * r) ≤ 3 * CE ^ 2 / c * L ^ 2 * N / r ^ 2 := by
    have hcr : 0 < c * r := by positivity
    rw [div_le_iff₀ hcr]
    have : 3 * CE ^ 2 / c * L ^ 2 * N / r ^ 2 * (c * r) = 3 * CE ^ 2 * L ^ 2 * N / r := by
      field_simp
    rw [this, le_div_iff₀ hr0]
    have hG2 : G * r ^ 2 ≤ 3 / 2 * L ^ 2 * N := by
      have := mul_le_mul_of_nonneg_right hG (sq_nonneg r)
      calc G * r ^ 2 ≤ 3 / 2 * (L / r) ^ 2 * N * r ^ 2 := this
        _ = 3 / 2 * L ^ 2 * N := by field_simp
    have hr2 : r ≤ r ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hG2 (by positivity : 0 ≤ 2 * CE ^ 2),
      mul_le_mul_of_nonneg_left hr2 (by positivity : 0 ≤ 2 * CE ^ 2 * G)]
  have hfirst : 3 / 2 * (L / r) ^ 2 * N = 3 / 2 * L ^ 2 * N / r ^ 2 := by field_simp
  have hm2 : c / 2 * m ≤ (3 / 2 + 3 * CE ^ 2 / c) * L ^ 2 * N / r ^ 2 := by
    have : (3 / 2 + 3 * CE ^ 2 / c) * L ^ 2 * N / r ^ 2 =
        3 / 2 * L ^ 2 * N / r ^ 2 + 3 * CE ^ 2 / c * L ^ 2 * N / r ^ 2 := by ring
    rw [this]; linarith
  have hA : 0 ≤ (3 / 2 + 3 * CE ^ 2 / c) * L ^ 2 := by positivity
  have hN' : (3 / 2 + 3 * CE ^ 2 / c) * L ^ 2 * N ≤
      (3 / 2 + 3 * CE ^ 2 / c) * L ^ 2 * (Real.sqrt CA * (1 + Real.sqrt D)) * Real.sqrt r := by
    have := mul_le_mul_of_nonneg_left hN hA
    linarith [this]
  have hsr_le : Real.sqrt r ≤ r := by nlinarith
  rw [le_div_iff₀ hr0]
  unfold tailConstant
  have hfin : m * r ^ 2 ≤ (2 / c) * ((3 / 2 + 3 * CE ^ 2 / c) * L ^ 2 * N) := by
    have h := hm2
    rw [le_div_iff₀ (by positivity)] at h
    have : m * r ^ 2 = (2 / c) * (c / 2 * m * r ^ 2) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hX : 0 ≤ (3 / 2 + 3 * CE ^ 2 / c) * L ^ 2 * (Real.sqrt CA * (1 + Real.sqrt D)) := by positivity
  have h2c : 0 < 2 / c := by positivity
  calc m * r = m * r ^ 2 / r := by field_simp
    _ ≤ (2 / c) * ((3 / 2 + 3 * CE ^ 2 / c) * L ^ 2 * N) / r :=
        div_le_div_of_nonneg_right hfin hr0.le
    _ ≤ (2 / c) * ((3 / 2 + 3 * CE ^ 2 / c) * L ^ 2 *
          (Real.sqrt CA * (1 + Real.sqrt D)) * Real.sqrt r) / r := by
        gcongr
    _ ≤ (2 / c) * ((3 / 2 + 3 * CE ^ 2 / c) * L ^ 2 *
          (Real.sqrt CA * (1 + Real.sqrt D)) * r) / r := by
        gcongr
    _ = 2 / c * (3 / 2 + 3 * CE ^ 2 / c) * L ^ 2 * Real.sqrt CA * (1 + Real.sqrt D) := by
        field_simp
