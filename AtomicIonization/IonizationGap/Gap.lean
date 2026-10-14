import AtomicIonization.IonizationGap.Average
import OAI.Analysis.CoulombRadii.LimitTheory.NeutralBaseline

/-!
# A uniform positive ionization gap

For large `Z`, let `Φ` be a ground state of the atom with `Z - 1` electrons and nuclear charge
`Z`. Its energy is within a universal offset of the unrestricted bottom of the spectrum. For a
center `y` in the shell `{T¹⁰ ≤ |y| < 2T¹⁰}`, the insertion of a packet of radius `T⁶` into a hole
cut around `y` gives a `Z`-electron trial state; the field lost on the discarded configurations is
controlled by the screening estimate in the complementary loss state. Averaging the center over the
shell recovers one unscreened unit of charge, while the kinetic and localization costs and the
expected near count are of lower order. A good center therefore exists, and
`E_Z ≤ E_Z(Z - 1) - 1/(4 T¹⁰)` for one universal `T`.
-/

namespace AtomicIonization.IonizationGap

open OAI OAI.NeutralAtom MeasureTheory

noncomputable section

/-- The cut gradient constant at unit scale. -/
def cutConstant : ℝ := 3 * Coulomb.radialCutCoefficient ^ 2 / 4

theorem cutConstant_nonneg : 0 ≤ cutConstant := by unfold cutConstant; positivity

theorem cutGradientConstant_two_mul {b : ℝ} (hb : 0 < b) :
    cutGradientConstant (2 * b) = cutConstant / b ^ 2 := by
  unfold cutGradientConstant cutConstant
  field_simp
  ring

theorem eps_bounds (N : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    1 / ((N + 1) * T ^ 20) ≤ 1 / T ^ 20 ∧ 1 / ((N + 1) * T ^ 20) * N ≤ 1 / T ^ 20 := by
  have hT20 : 0 < T ^ 20 := pow_pos (by linarith) 20
  have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
  constructor
  · apply one_div_le_one_div_of_le hT20
    nlinarith
  · rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hT20]
    nlinarith

/-- The scalar inequalities behind the bound at one center. -/
theorem center_algebra {T a ε Nr A p Ny EH HF HL kin0 K0 D Cf P Q : ℝ}
    (hT : 400 ≤ T) (haT : T ^ 8 ≤ a) (hε : 0 < ε) (hεT : ε ≤ 1 / T ^ 20)
    (hεN : ε * Nr ≤ 1 / T ^ 20) (hK0 : 0 ≤ K0) (hkin0 : 0 ≤ kin0) (hD : 0 ≤ D) (hCf : 0 ≤ Cf)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hp0 : 0 ≤ p) (hpN : p ≤ Ny) (hNy0 : 0 ≤ Ny)
    (hsplit : EH = HF + HL)
    (ins : Q * A ≤ (1 / 2 : ℝ) * (K0 / T ^ 12) * Ny + (1 / 2 : ℝ) * (kin0 / T ^ 12) * A - HF)
    (loss : HL ≤ Cf * Real.sqrt P * ((p + ε) / a +
        ((1 + D) * (p + ε) + (1 / 2 : ℝ) * (K0 / T ^ 12) * Ny) / (2 * Real.sqrt a)) +
      ε * Nr / (40 * a)) :
    Q * A ≤ (kin0 / 2 + Cf * Real.sqrt P * (2 + D + K0) + 1) / T ^ 12 +
      (K0 / 2 + Cf * Real.sqrt P * (2 + D + K0)) * Ny / T ^ 4 - EH := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hpow : ∀ k m : ℕ, k ≤ m → T ^ k ≤ T ^ m := fun k m h => pow_le_pow_right₀ hT1 h
  have hTk : ∀ k : ℕ, 0 < T ^ k := fun k => pow_pos hT0 k
  have ha1 : 1 ≤ a := le_trans (one_le_pow₀ hT1) haT
  have ha0 : 0 < a := by linarith
  set Λ := Cf * Real.sqrt P * (2 + D + K0) with hΛdef
  have hsP : 0 ≤ Cf * Real.sqrt P := mul_nonneg hCf (Real.sqrt_nonneg _)
  have hΛ : 0 ≤ Λ := by positivity
  have hT4 := hTk 4
  have hT12 := hTk 12
  have hsa : T ^ 4 ≤ Real.sqrt a := by
    apply Real.le_sqrt_of_sq_le
    calc (T ^ 4) ^ 2 = T ^ 8 := by ring
      _ ≤ a := haT
  have hP1 : (1 / 2 : ℝ) * (K0 / T ^ 12) * Ny ≤ K0 / 2 * Ny / T ^ 4 := by
    have h1 : K0 / T ^ 12 ≤ K0 / T ^ 4 :=
      div_le_div_of_nonneg_left hK0 hT4 (hpow 4 12 (by norm_num))
    have h2 : (1 / 2 : ℝ) * (K0 / T ^ 12) * Ny ≤ (1 / 2 : ℝ) * (K0 / T ^ 4) * Ny := by
      gcongr
    calc _ ≤ (1 / 2 : ℝ) * (K0 / T ^ 4) * Ny := h2
      _ = K0 / 2 * Ny / T ^ 4 := by ring
  have hP2 : (1 / 2 : ℝ) * (kin0 / T ^ 12) * A ≤ kin0 / 2 / T ^ 12 := by
    calc (1 / 2 : ℝ) * (kin0 / T ^ 12) * A ≤ (1 / 2 : ℝ) * (kin0 / T ^ 12) * 1 := by
          gcongr
      _ = kin0 / 2 / T ^ 12 := by ring
  have hq1 : (p + ε) / a ≤ (Ny + ε) / T ^ 4 :=
    div_le_div₀ (by linarith) (by linarith) hT4 ((hpow 4 8 (by norm_num)).trans haT)
  have hK12 : K0 / T ^ 12 ≤ K0 := div_le_self hK0 (one_le_pow₀ hT1)
  have hq2 : ((1 + D) * (p + ε) + (1 / 2 : ℝ) * (K0 / T ^ 12) * Ny) / (2 * Real.sqrt a) ≤
      ((1 + D) * (Ny + ε) + (1 / 2 : ℝ) * K0 * Ny) / (2 * T ^ 4) := by
    have h1 : (1 + D) * (p + ε) ≤ (1 + D) * (Ny + ε) := by gcongr
    have h2 : (1 / 2 : ℝ) * (K0 / T ^ 12) * Ny ≤ (1 / 2 : ℝ) * K0 * Ny := by gcongr
    have hnum : 0 ≤ (1 + D) * (Ny + ε) + (1 / 2 : ℝ) * K0 * Ny := by positivity
    exact div_le_div₀ hnum (by linarith) (by positivity) (by linarith)
  have hq3 : (Ny + ε) / T ^ 4 + ((1 + D) * (Ny + ε) + (1 / 2 : ℝ) * K0 * Ny) / (2 * T ^ 4) ≤
      (2 + D + K0) * (Ny + ε) / T ^ 4 := by
    have he : (Ny + ε) / T ^ 4 + ((1 + D) * (Ny + ε) + (1 / 2 : ℝ) * K0 * Ny) / (2 * T ^ 4) =
        ((Ny + ε) + ((1 + D) * (Ny + ε) + (1 / 2 : ℝ) * K0 * Ny) / 2) / T ^ 4 := by
      field_simp
    rw [he]
    apply div_le_div_of_nonneg_right _ hT4.le
    nlinarith [mul_nonneg hD hNy0, mul_nonneg hK0 hNy0, mul_nonneg hK0 hε.le, mul_nonneg hD hε.le]
  have hq4 : ε / T ^ 4 ≤ 1 / T ^ 12 := by
    have h1 : 1 / T ^ 20 ≤ 1 / T ^ 8 := one_div_le_one_div_of_le (hTk 8) (hpow 8 20 (by norm_num))
    calc ε / T ^ 4 ≤ (1 / T ^ 8) / T ^ 4 := div_le_div_of_nonneg_right (hεT.trans h1) hT4.le
      _ = 1 / T ^ 12 := by rw [div_div, ← pow_add]
  have hq5 : ε * Nr / (40 * a) ≤ 1 / T ^ 12 := by
    have h2 : 1 / T ^ 20 ≤ 1 / T ^ 12 := one_div_le_one_div_of_le hT12 (hpow 12 20 (by norm_num))
    have hεN0 : 0 ≤ ε * Nr ∨ ε * Nr < 0 := le_or_gt 0 (ε * Nr)
    rcases hεN0 with h0 | h0
    · have h3 : ε * Nr / (40 * a) ≤ ε * Nr := div_le_self h0 (by linarith)
      linarith
    · have h3 : ε * Nr / (40 * a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h0.le (by linarith)
      have h4 : 0 ≤ 1 / T ^ 12 := by positivity
      linarith
  have hloss : HL ≤ Λ * Ny / T ^ 4 + Λ / T ^ 12 + 1 / T ^ 12 := by
    have h1 : Cf * Real.sqrt P * ((p + ε) / a + ((1 + D) * (p + ε) +
        (1 / 2 : ℝ) * (K0 / T ^ 12) * Ny) / (2 * Real.sqrt a)) ≤
        Cf * Real.sqrt P * ((2 + D + K0) * (Ny + ε) / T ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ hsP
      linarith
    have h2 : Cf * Real.sqrt P * ((2 + D + K0) * (Ny + ε) / T ^ 4) =
        Λ * Ny / T ^ 4 + Λ * (ε / T ^ 4) := by rw [hΛdef]; ring
    have h3 : Λ * (ε / T ^ 4) ≤ Λ * (1 / T ^ 12) := mul_le_mul_of_nonneg_left hq4 hΛ
    have h4 : Λ * (1 / T ^ 12) = Λ / T ^ 12 := by ring
    linarith
  have hgoal1 : (kin0 / 2 + Λ + 1) / T ^ 12 = kin0 / 2 / T ^ 12 + Λ / T ^ 12 + 1 / T ^ 12 := by
    ring
  have hgoal2 : (K0 / 2 + Λ) * Ny / T ^ 4 = K0 / 2 * Ny / T ^ 4 + Λ * Ny / T ^ 4 := by ring
  rw [hgoal1, hgoal2]
  linarith

/-- The bound at one center of the shell. -/
theorem center_bound {N : ℕ} {Φ : Wavefunction N} {g : Gradient N}
    (hd : FormDomain Φ g) (hn : normSquared Φ = 1)
    (hmin : ∀ (χ : Wavefunction N) (h : Gradient N),
      FormDomain χ h → normSquared χ = 1 → energy (N + 1) Φ g ≤ energy (N + 1) χ h)
    {E' : ℝ} (hE' : ∀ (χ : Wavefunction (N + 1)) (h : Gradient (N + 1)),
      FormDomain χ h → normSquared χ = 1 → E' ≤ energy (N + 1) χ h)
    {Eg D Cf P : ℝ} (hD : 0 ≤ D) (hCf : 0 ≤ Cf) (hP : 1 ≤ P)
    (hED : energy (N + 1) Φ g ≤ Eg + D)
    (hfield : ∀ {y : Position}, y ≠ 0 → ∀ {ψ : Wavefunction N} {h : Gradient N},
      FormDomain ψ h → normSquared ψ = 1 →
      ∀ {δ : ℝ}, energy (N + 1) ψ h ≤ Eg + δ → 0 ≤ δ →
        ((N + 1 : ℕ) : ℝ) * ‖y‖⁻¹ - farPotential ψ y (40 * (‖y‖ / 100000)) ≤
          Cf * (Real.sqrt P * Coulomb.screenMass δ (‖y‖ / 100000) / (‖y‖ / 100000)))
    {T : ℝ} (hT : 400 ≤ T) {y : Position} (hy : T ^ 10 ≤ ‖y‖) :
    (E' - energy (N + 1) Φ g) * wexp Φ (fun x => coreProduct y (2 * T ^ 6) x ^ 2) ≤
      (Coulomb.unitWindowKinetic / 2 + Cf * Real.sqrt P * (2 + D + cutConstant) + 1) / T ^ 12 +
      (cutConstant / 2 + Cf * Real.sqrt P * (2 + D + cutConstant)) *
        wexp Φ (nearCount y (2 * T ^ 6)) / T ^ 4 -
      wexp Φ (insertionField (N + 1) (T ^ 6) y) := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hpow : ∀ k m : ℕ, k ≤ m → T ^ k ≤ T ^ m := fun k m h => pow_le_pow_right₀ hT1 h
  have hTk : ∀ k : ℕ, 0 < T ^ k := fun k => pow_pos hT0 k
  set b := T ^ 6 with hbdef
  have hb : 0 < b := hTk 6
  have hyb : b < ‖y‖ :=
    lt_of_lt_of_le (pow_lt_pow_right₀ (by linarith) (by norm_num : 6 < 10)) hy
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hy
    linarith [hTk 10]
  set a := ‖y‖ / 100000 with hadef
  have haT : T ^ 8 ≤ a := by
    have h2 : (100000 : ℝ) ≤ T ^ 2 := by nlinarith
    have h3 : T ^ 10 = T ^ 8 * T ^ 2 := by ring
    rw [hadef, le_div_iff₀ (by norm_num)]
    nlinarith [hTk 8]
  have ha1 : 1 ≤ a := le_trans (one_le_pow₀ hT1) haT
  have ha0 : 0 < a := by linarith
  have hb40 : b ≤ 40 * a := by have := hpow 6 8 (by norm_num); linarith
  set ε : ℝ := 1 / ((N + 1) * T ^ 20) with hεdef
  have hε : 0 < ε := by positivity
  have ins := insertion_inequality hd hn hmin hE' hb hyb
  have loss := loss_bound hd hn hmin hD hCf hP hED hy0 (hfield hy0) hb hb40 ha1 hε
  set F : Configuration N → ℝ := coreProduct y (2 * b) with hFdef
  set A := wexp Φ (fun x => F x ^ 2) with hAdef
  set p := wexp Φ (fun x => 1 - F x ^ 2) with hpdef
  set Ny := wexp Φ (nearCount y (2 * b)) with hNydef
  set EH := wexp Φ (insertionField (N + 1) b y) with hEHdef
  set K0 := cutConstant with hK0def
  have hK0 : 0 ≤ K0 := cutConstant_nonneg
  have hK : cutGradientConstant (2 * b) = K0 / T ^ 12 := by
    rw [cutGradientConstant_two_mul hb, hbdef]; ring
  rw [hK] at ins loss
  have hψ := hd.2.2.1
  have hr : 0 < 2 * b := by linarith
  have hFm : Measurable F := (coreProduct_multiplier (n := N) y hr).smooth.continuous.measurable
  have hF01 : ∀ x, 0 ≤ F x ^ 2 ∧ F x ^ 2 ≤ 1 := by
    intro x
    have h0 := coreProduct_nonneg (n := N) y (2 * b) x
    have h1 := coreProduct_le_one (n := N) y (2 * b) x
    constructor <;> nlinarith
  obtain ⟨CH, hCH⟩ := insertionField_abs_le (N + 1) hb
  have hHm : Measurable (insertionField (N + 1) b y (n := N)) :=
    (insertionField_measurable (N + 1) b (n := N)).of_uncurry_left
  have hHb : ∀ x : Configuration N, |insertionField (N + 1) b y x| ≤ ((N + 1 : ℕ) + N) * CH :=
    fun x => hCH y x
  have hsplit : EH = wexp Φ (fun x => insertionField (N + 1) b y x * F x ^ 2) +
      wexp Φ (fun x => insertionField (N + 1) b y x * (1 - F x ^ 2)) := by
    rw [← wexp_add hψ]
    · rw [hEHdef]
      congr 1
      funext x
      ring
    · exact integrable_bounded_weight hψ (hHm.mul (hFm.pow_const 2))
        (C := ((N + 1 : ℕ) + N) * CH) (fun x => by
          rw [abs_mul, abs_of_nonneg (hF01 x).1]
          have h0 : 0 ≤ ((N + 1 : ℕ) + (N : ℝ)) * CH := (abs_nonneg _).trans (hHb x)
          nlinarith [hHb x, (hF01 x).2, abs_nonneg (insertionField (N + 1) b y x)])
    · exact integrable_bounded_weight hψ (hHm.mul (measurable_const.sub (hFm.pow_const 2)))
        (C := ((N + 1 : ℕ) + N) * CH) (fun x => by
          have h1 : 0 ≤ 1 - F x ^ 2 := by linarith [(hF01 x).2]
          rw [abs_mul, abs_of_nonneg h1]
          have h0 : 0 ≤ ((N + 1 : ℕ) + (N : ℝ)) * CH := (abs_nonneg _).trans (hHb x)
          nlinarith [hHb x, (hF01 x).1, abs_nonneg (insertionField (N + 1) b y x)])
  have hNm : Measurable (nearCount y (2 * b) (n := N)) :=
    (nearCount_measurable (2 * b) (n := N)).of_uncurry_left
  have hNb : ∀ x : Configuration N, |nearCount y (2 * b) x| ≤ N := fun x => by
    rw [abs_of_nonneg (nearCount_nonneg _ _ _)]; exact nearCount_le _ _ _
  have hpN : p ≤ Ny := by
    apply wexp_mono
    · exact integrable_bounded_weight hψ (measurable_const.sub (hFm.pow_const 2)) (C := 1)
        (fun x => by rw [abs_le]; constructor <;> linarith [(hF01 x).1, (hF01 x).2])
    · exact integrable_bounded_weight hψ hNm hNb
    · exact fun x => one_sub_coreProduct_sq_le y hr x
  have hA0 : 0 ≤ A := wexp_nonneg Φ (fun x => (hF01 x).1)
  have hA1 : A ≤ 1 := by
    have h := wexp_mono (ψ := Φ) (V := fun x => F x ^ 2) (W := fun _ => (1 : ℝ))
      (integrable_bounded_weight hψ (hFm.pow_const 2) (C := 1)
        (fun x => by rw [abs_of_nonneg (hF01 x).1]; exact (hF01 x).2))
      (integrable_bounded_weight hψ measurable_const (C := 1) (fun _ => by norm_num))
      (fun x => (hF01 x).2)
    rwa [wexp_one, hn] at h
  have hNy0 : 0 ≤ Ny := wexp_nonneg Φ (nearCount_nonneg _ _)
  have hp0 : 0 ≤ p := wexp_nonneg Φ (fun x => by linarith [(hF01 x).2])
  have hb2 : b ^ 2 = T ^ 12 := by rw [hbdef]; ring
  rw [hb2] at ins
  obtain ⟨hεT, hεN⟩ := eps_bounds N hT1
  rw [← hεdef] at hεT hεN
  have hrw : wexp Φ (fun x => insertionField (N + 1) b y x * coreProduct y (2 * b) x ^ 2) =
      wexp Φ (fun x => insertionField (N + 1) b y x * F x ^ 2) := rfl
  rw [hrw] at ins
  exact center_algebra hT haT hε hεT hεN cutConstant_nonneg Coulomb.unitWindowKinetic_nonneg hD hCf
    hA0 hA1 hp0 hpN hNy0 hsplit ins loss

theorem wexp_count {n : ℕ} {Φ : Wavefunction n} (hΦ : ∀ σ, MemLp (Φ σ) 2 volume)
    {A : Set Position} (hA : MeasurableSet A) :
    wexp Φ (fun x => ∑ i, A.indicator (fun _ => (1 : ℝ)) (x i)) = populationOf Φ A := by
  unfold wexp populationOf
  apply Finset.sum_congr rfl
  intro σ _
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum]
  intro i _
  refine integrable_bounded_weight hΦ ((measurable_const.indicator hA).comp (measurable_pi_apply i))
    (C := 1) (fun x => ?_) σ
  simp only [Function.comp_apply]
  by_cases h : x i ∈ A
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num

theorem core_weight_bounds {n : ℕ} {Φ : Wavefunction n} (hΦ : ∀ σ, MemLp (Φ σ) 2 volume)
    (hn : normSquared Φ = 1) (y : Position) {r : ℝ} (hr : 0 < r) :
    0 ≤ wexp Φ (fun x => coreProduct y r x ^ 2) ∧ wexp Φ (fun x => coreProduct y r x ^ 2) ≤ 1 := by
  have hF01 : ∀ x : Configuration n, 0 ≤ coreProduct y r x ^ 2 ∧ coreProduct y r x ^ 2 ≤ 1 := by
    intro x
    have h0 := coreProduct_nonneg (n := n) y r x
    have h1 := coreProduct_le_one (n := n) y r x
    constructor <;> nlinarith
  have hFm : Measurable (coreProduct (n := n) y r) :=
    (coreProduct_multiplier (n := n) y hr).smooth.continuous.measurable
  refine ⟨wexp_nonneg Φ (fun x => (hF01 x).1), ?_⟩
  have h := wexp_mono (ψ := Φ) (V := fun x => coreProduct y r x ^ 2) (W := fun _ => (1 : ℝ))
    (integrable_bounded_weight hΦ (hFm.pow_const 2) (C := 1)
      (fun x => by rw [abs_of_nonneg (hF01 x).1]; exact (hF01 x).2))
    (integrable_bounded_weight hΦ measurable_const (C := 1) (fun _ => by norm_num))
    (fun x => (hF01 x).2)
  rwa [wexp_one, hn] at h

theorem gap_conclude {Q A R c : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (h : Q * A ≤ R) (hR : R < -c)
    (hc : 0 < c) : Q ≤ -c := by
  by_cases hQ : 0 ≤ Q
  · nlinarith [mul_nonneg hQ hA0]
  · push_neg at hQ
    nlinarith

theorem gap_scalar {T A1 A2 : ℝ} (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hT : A1 + A2 + 400 ≤ T) :
    A1 * T ^ 18 + A2 * T ^ 19 - 14 * Real.pi / 3 * T ^ 20 < -(7 * Real.pi / 3 * T ^ 20) := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have h18 : 0 < T ^ 18 := pow_pos hT0 18
  have h1 : A1 * T ^ 18 ≤ A1 * T ^ 19 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT1 (by norm_num)) hA1
  have h2 : (A1 + A2) * T ^ 19 < T * T ^ 19 :=
    mul_lt_mul_of_pos_right (by linarith) (pow_pos hT0 19)
  have h3 : T * T ^ 19 = T ^ 20 := by ring
  have hpi := Real.pi_gt_three
  have h20 : 0 < T ^ 20 := pow_pos hT0 20
  nlinarith

theorem screenMass_power_bound {D T : ℝ} (hD : 0 ≤ D) (hT : 2 ≤ T) :
    Coulomb.screenMass D (T ^ 10) ≤ (1 + D) * T ^ 5 := by
  have hT0 : 0 < T := by linarith
  have h5 : 2 ≤ T ^ 5 := le_trans hT (le_self_pow₀ (by linarith) (by norm_num))
  have hbase : Coulomb.screenBaseMass (T ^ 10) = 1 := by
    unfold Coulomb.screenBaseMass
    exact max_eq_right (inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_pow₀ (by linarith))))
  have hs : Real.sqrt (D * T ^ 10) = Real.sqrt D * T ^ 5 := by
    rw [Real.sqrt_mul hD, show T ^ 10 = (T ^ 5) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  unfold Coulomb.screenMass
  rw [hbase, hs]
  have hsD := sqrt_le_half_one_add hD
  have h1 : Real.sqrt D * T ^ 5 ≤ (1 + D) / 2 * T ^ 5 :=
    mul_le_mul_of_nonneg_right hsD (by positivity)
  nlinarith

set_option maxHeartbeats 1000000 in
/-- The ionization gap for the ground states of the singly ionized atoms of large charge. -/
theorem gap_core : ∃ c : ℝ, 0 < c ∧ ∃ Z₂ : ℕ, ∀ N : ℕ, Z₂ ≤ N + 1 →
    ∀ {Φ : Wavefunction N} {g : Gradient N}, FormDomain Φ g → normSquared Φ = 1 →
    (∀ (χ : Wavefunction N) (h : Gradient N), FormDomain χ h → normSquared χ = 1 →
      energy (N + 1) Φ g ≤ energy (N + 1) χ h) →
    ((energy (N + 1) Φ g : ℝ) : EReal) =
      Coulomb.sectorFormBottom (Coulomb.atom (N + 1) (Nat.le_add_left 1 N)) N →
    ∀ {E' : ℝ}, (∀ (χ : Wavefunction (N + 1)) (h : Gradient (N + 1)),
      FormDomain χ h → normSquared χ = 1 → E' ≤ energy (N + 1) χ h) →
    E' ≤ energy (N + 1) Φ g - c := by
  obtain ⟨D, hD, Zmin, Hoff⟩ := physical_uniform_predecessor_offset
  obtain ⟨Cf, P, hCf, hP, Hfield⟩ := far_field_bound
  obtain ⟨Cann, hCann, Hann⟩ := annular_population_bound
  set kin0 := Coulomb.unitWindowKinetic with hkin0def
  have hkin0 : 0 ≤ kin0 := Coulomb.unitWindowKinetic_nonneg
  set K0 := cutConstant with hK0def
  have hK0 : 0 ≤ K0 := cutConstant_nonneg
  set Λ := Cf * Real.sqrt P * (2 + D + K0) with hΛdef
  have hΛ : 0 ≤ Λ := by positivity
  set c0 := kin0 / 2 + Λ + 1 with hc0def
  set c1 := K0 / 2 + Λ with hc1def
  have hc0 : 0 ≤ c0 := by positivity
  have hc1 : 0 ≤ c1 := by positivity
  set A1 := 28 * Real.pi / 3 * c0 with hA1def
  set A2 := 256 * Real.pi / 3 * c1 * Cann * (1 + D) with hA2def
  have hA1 : 0 ≤ A1 := by positivity
  have hA2 : 0 ≤ A2 := by positivity
  set T : ℝ := ((⌈A1 + A2⌉₊ : ℕ) : ℝ) + 400 with hTdef
  have hTA : A1 + A2 + 400 ≤ T := by
    have := Nat.le_ceil (A1 + A2)
    linarith
  have hT400 : 400 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hTk : ∀ k : ℕ, 0 < T ^ k := fun k => pow_pos hT0 k
  refine ⟨1 / (4 * T ^ 10), by positivity, Zmin, ?_⟩
  intro N hN Φ g hd hn hmin hsec E' hE'
  have hZ : 1 ≤ N + 1 := Nat.le_add_left 1 N
  set E := energy (N + 1) Φ g with hEdef
  set Eg := (Coulomb.unrestrictedFormBottom (Coulomb.atom (N + 1) hZ)).toReal with hEgdef
  have hEgle : (Eg : EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom (N + 1) hZ) :=
    (Coulomb.atom_unrestricted_bottom_real (N + 1) hZ (asH1 Φ g hd.2.1 hd.2.2.1 hd.2.2.2.1)
      (asH1_antisymmetric hd) ((asH1_mass _ _ _).trans hn)).le
  have hED : E ≤ Eg + D := by
    have h := Hoff (N + 1) hN hZ
    have he : (Coulomb.sectorFormBottom (Coulomb.atom (N + 1) hZ) (N + 1 - 1)).toReal = E := by
      rw [Nat.add_sub_cancel, ← hsec, EReal.toReal_coe]
    rw [he] at h
    exact h
  have hfield : ∀ {y : Position}, y ≠ 0 → ∀ {ψ : Wavefunction N} {h : Gradient N},
      FormDomain ψ h → normSquared ψ = 1 →
      ∀ {δ : ℝ}, energy (N + 1) ψ h ≤ Eg + δ → 0 ≤ δ →
        ((N + 1 : ℕ) : ℝ) * ‖y‖⁻¹ - farPotential ψ y (40 * (‖y‖ / 100000)) ≤
          Cf * (Real.sqrt P * Coulomb.screenMass δ (‖y‖ / 100000) / (‖y‖ / 100000)) :=
    by
      intro y hy ψ h hψ hn' δ hδ hδ0
      exact Hfield (N + 1) hZ hψ hn' hEgle hδ hδ0 hy
  have hψΦ := hd.2.2.1
  set S := T ^ 10 with hSdef
  have hS : 0 < S := hTk 10
  set r := 2 * T ^ 6 with hrdef
  have hr : 0 < r := by positivity
  have h6 : T ^ 6 ≤ T ^ 10 := pow_le_pow_right₀ hT1 (by norm_num)
  have hrS : 2 * r < S / 2 := by
    have h4 : 16 ≤ T ^ 4 := by
      have : (16 : ℝ) ≤ 400 ^ 4 := by norm_num
      exact this.trans (pow_le_pow_left₀ (by norm_num) hT400 4)
    have he : S = T ^ 6 * T ^ 4 := by rw [hSdef]; ring
    rw [hrdef, he]
    nlinarith [hTk 6]
  set ρ := Coulomb.radialShellDensity S with hρdef
  have hρi : Integrable ρ := Coulomb.radialShellDensity_integrable S
  have hρm : Measurable ρ := Coulomb.radialShellDensity_measurable S
  have hρ0 : ∀ y, 0 ≤ ρ y := Coulomb.radialShellDensity_nonneg S
  set Ny : Position → ℝ := fun y => wexp Φ (nearCount y r) with hNydef
  set EH : Position → ℝ := fun y => wexp Φ (insertionField (N + 1) (T ^ 6) y) with hEHdef
  set R : Position → ℝ := fun y => c0 / T ^ 12 + c1 * Ny y / T ^ 4 - EH y with hRdef
  have hcenter : ∀ y, ρ y ≠ 0 →
      (E' - E) * wexp Φ (fun x => coreProduct y r x ^ 2) ≤ R y := by
    intro y hy
    have hyS : T ^ 10 ≤ ‖y‖ := by
      by_contra h
      exact hy (Coulomb.radialShellDensity_zero_inner (lt_of_not_ge h))
    exact center_bound hd hn hmin hE' hD hCf hP hED hfield hT400 hyS
  obtain ⟨CH, hCH⟩ := insertionField_abs_le (N + 1) (hTk 6)
  obtain ⟨hIN, hEN, -⟩ := average_wexp hψΦ hρi hρm (W := fun y => nearCount y r)
    (nearCount_measurable r) (C := N)
    (fun y x => by rw [abs_of_nonneg (nearCount_nonneg _ _ _)]; exact nearCount_le _ _ _)
  obtain ⟨hIH, hEH', hIH'⟩ := average_wexp hψΦ hρi hρm
    (W := fun y => insertionField (N + 1) (T ^ 6) y)
    (insertionField_measurable _ _) (fun y x => hCH y x)
  have hRfun : (fun y => ρ y * R y) =
      fun y => c0 / T ^ 12 * ρ y + c1 / T ^ 4 * (ρ y * Ny y) - ρ y * EH y := by
    funext y
    simp only [hRdef]
    ring
  have hI1 : Integrable (fun y => c0 / T ^ 12 * ρ y + c1 / T ^ 4 * (ρ y * Ny y)) :=
    (hρi.const_mul _).add (hIN.const_mul _)
  have hIR : Integrable (fun y => ρ y * R y) := by
    rw [hRfun]
    exact hI1.sub hIH
  have hintR : (∫ y, ρ y * R y) = c0 / T ^ 12 * (∫ y, ρ y) +
      c1 / T ^ 4 * (∫ y, ρ y * Ny y) - ∫ y, ρ y * EH y := by
    rw [hRfun, integral_sub hI1 hIH, integral_add (hρi.const_mul _) (hIN.const_mul _),
      integral_const_mul, integral_const_mul]
  have hvol : (∫ y, ρ y) = 28 * Real.pi / 3 * S ^ 3 := Coulomb.radialShellDensity_mass hS
  -- the averaged near count
  set Ann : Set Position := {z : Position | 1 / 2 * S < ‖z‖ ∧ ‖z‖ < 3 * S} with hAnndef
  have hAnn : MeasurableSet Ann :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have hpop := Hann (N + 1) hZ hd hn hEgle (δ := D) hED hD hS
  have hsm := screenMass_power_bound hD (T := T) (by linarith)
  have hNav : (∫ y, ρ y * Ny y) ≤
      4 * Real.pi / 3 * (2 * r) ^ 3 * (Cann * ((1 + D) * T ^ 5)) := by
    have h1 : (∫ y, ρ y * Ny y) = wexp Φ (fun x => ∫ y, ρ y * nearCount y r x) := hEN
    have h2 : wexp Φ (fun x => ∫ y, ρ y * nearCount y r x) ≤
        wexp Φ (fun x => 4 * Real.pi / 3 * (2 * r) ^ 3 *
          ∑ i, Ann.indicator (fun _ => (1 : ℝ)) (x i)) := by
      apply Finset.sum_le_sum
      intro σ _
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x => mul_nonneg (integral_nonneg fun y =>
          mul_nonneg (hρ0 y) (nearCount_nonneg _ _ _)) (sq_nonneg _)
      · refine integrable_bounded_weight hψΦ (W := fun x => 4 * Real.pi / 3 * (2 * r) ^ 3 *
          ∑ i, Ann.indicator (fun _ => (1 : ℝ)) (x i)) (measurable_const.mul (Finset.measurable_sum _
          fun i _ => (measurable_const.indicator hAnn).comp (measurable_pi_apply i)))
          (C := 4 * Real.pi / 3 * (2 * r) ^ 3 * N) (fun x => ?_) σ
        have hc0 : 0 ≤ ∑ i, Ann.indicator (fun _ => (1 : ℝ)) (x i) :=
          Finset.sum_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
        have hc1 : ∑ i, Ann.indicator (fun _ => (1 : ℝ)) (x i) ≤ N := by
          calc _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
                Set.indicator_le_self' (fun _ _ => zero_le_one) _
            _ = N := by simp
        have hv : 0 ≤ 4 * Real.pi / 3 * (2 * r) ^ 3 := by positivity
        rw [abs_of_nonneg (mul_nonneg hv hc0)]
        exact mul_le_mul_of_nonneg_left hc1 hv
      · exact Filter.Eventually.of_forall fun x =>
          mul_le_mul_of_nonneg_right (shell_average_near hr hrS x) (sq_nonneg _)
    have h3 : wexp Φ (fun x => 4 * Real.pi / 3 * (2 * r) ^ 3 *
        ∑ i, Ann.indicator (fun _ => (1 : ℝ)) (x i)) =
        4 * Real.pi / 3 * (2 * r) ^ 3 * populationOf Φ Ann := by
      rw [wexp_const_mul, wexp_count hψΦ hAnn]
    have h4 : populationOf Φ Ann ≤ Cann * ((1 + D) * T ^ 5) :=
      hpop.trans (mul_le_mul_of_nonneg_left hsm hCann)
    have h5 : 0 ≤ 4 * Real.pi / 3 * (2 * r) ^ 3 := by positivity
    calc _ = _ := h1
      _ ≤ _ := h2
      _ = _ := h3
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 h5
  -- the averaged field
  have hHav : Coulomb.radialShellMoment S ≤ ∫ y, ρ y * EH y := by
    have h1 : (∫ y, ρ y * EH y) = wexp Φ (fun x => ∫ y, ρ y * insertionField (N + 1) (T ^ 6) y x) :=
      hEH'
    rw [h1]
    have h2 : wexp Φ (fun _ => Coulomb.radialShellMoment S * 1) =
        Coulomb.radialShellMoment S := by rw [wexp_const_mul, wexp_one, hn, mul_one]
    rw [← h2]
    apply wexp_mono
    · exact integrable_bounded_weight hψΦ measurable_const (C := |Coulomb.radialShellMoment S * 1|)
        (fun _ => le_rfl)
    · exact hIH'
    · intro x
      rw [mul_one]
      exact shell_average_field hS (hTk 6) h6 x
  have hmom := Coulomb.radialShellMoment_lower hS
  rw [hvol] at hmom
  set c := 1 / (4 * T ^ 10) with hcdef
  have hc : 0 < c := by positivity
  have e1 : c0 / T ^ 12 * (28 * Real.pi / 3 * S ^ 3) = A1 * T ^ 18 := by
    rw [hSdef, hA1def]; field_simp
  have e2 : c1 / T ^ 4 * (4 * Real.pi / 3 * (2 * r) ^ 3 * (Cann * ((1 + D) * T ^ 5))) =
      A2 * T ^ 19 := by
    rw [hrdef, hA2def]; field_simp; ring
  have e3 : 28 * Real.pi / 3 * S ^ 3 / (2 * S) = 14 * Real.pi / 3 * T ^ 20 := by
    rw [hSdef]; field_simp; ring
  have e4 : (28 * Real.pi / 3 * S ^ 3) * (-c) = -(7 * Real.pi / 3 * T ^ 20) := by
    rw [hSdef, hcdef]; field_simp; ring
  have hc1T : 0 ≤ c1 / T ^ 4 := by positivity
  have hbound : (∫ y, ρ y * R y) < -(7 * Real.pi / 3 * T ^ 20) := by
    rw [hintR, hvol, e1]
    have h1 := mul_le_mul_of_nonneg_left hNav hc1T
    rw [e2] at h1
    have h2 := gap_scalar hA1 hA2 hTA
    rw [e3] at hmom
    linarith
  have hex : ∃ y, ρ y ≠ 0 ∧ R y < -c := by
    by_contra hne
    simp only [not_exists, not_and, not_lt] at hne
    have hmono : (∫ y, ρ y * (-c)) ≤ ∫ y, ρ y * R y := by
      apply integral_mono (hρi.mul_const _) hIR
      intro y
      by_cases h : ρ y = 0
      · simp [h]
      · exact mul_le_mul_of_nonneg_left (hne y h) (hρ0 y)
    rw [integral_mul_const, hvol, e4] at hmono
    linarith
  obtain ⟨y, hy, hRy⟩ := hex
  obtain ⟨hA0, hA1'⟩ := core_weight_bounds hψΦ hn y hr
  have h := gap_conclude hA0 hA1' (hcenter y hy) hRy hc
  linarith

end

end AtomicIonization.IonizationGap
