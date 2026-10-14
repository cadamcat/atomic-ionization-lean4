import AtomicIonization.IonizationGap.Cut
import AtomicIonization.IonizationGap.Insert
import AtomicIonization.IonizationGap.Transfer

/-!
# The insertion inequality at one center

Let `Φ` be a normalized minimizer of the `N`-electron atom of charge `N + 1` with energy `E`, and
let `E'` be a lower bound for the energies of normalized `(N + 1)`-electron states. Cutting a hole
of radius `2b` around a center `y` with the symmetric multiplier `F = coreProduct y (2b)` and
inserting the packet of radius `b` there gives

  `(E' - E) A ≤ ½ K N_y + ½ (T/b²) A - E_Φ[F² H_y]`,

where `A = E_Φ F²`, `N_y` is the expected near count, `K` the cut gradient constant, `T` the unit
window kinetic energy and `H_y` the packet-averaged field. The field lost on the discarded
configurations, `E_Φ[(1 - F²) H_y]`, is bounded with the screening estimate applied to the
normalized loss state `√(1 + ε - F²) Φ`.
-/

namespace AtomicIonization.IonizationGap

open OAI OAI.NeutralAtom MeasureTheory

noncomputable section

/-- Weighted expectation `Σ_σ ∫ W |ψ|²`. -/
def wexp {n : ℕ} (ψ : Wavefunction n) (W : Configuration n → ℝ) : ℝ :=
  ∑ σ, ∫ x, W x * ‖ψ σ x‖ ^ 2

theorem wexp_add {n : ℕ} {ψ : Wavefunction n} (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    {V W : Configuration n → ℝ}
    (hV : ∀ σ, Integrable (fun x => V x * ‖ψ σ x‖ ^ 2))
    (hW : ∀ σ, Integrable (fun x => W x * ‖ψ σ x‖ ^ 2)) :
    wexp ψ (fun x => V x + W x) = wexp ψ V + wexp ψ W := by
  unfold wexp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← integral_add (hV σ) (hW σ)]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem wexp_const_mul {n : ℕ} (ψ : Wavefunction n) (c : ℝ) (W : Configuration n → ℝ) :
    wexp ψ (fun x => c * W x) = c * wexp ψ W := by
  unfold wexp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem wexp_mono {n : ℕ} {ψ : Wavefunction n} {V W : Configuration n → ℝ}
    (hV : ∀ σ, Integrable (fun x => V x * ‖ψ σ x‖ ^ 2))
    (hW : ∀ σ, Integrable (fun x => W x * ‖ψ σ x‖ ^ 2)) (h : ∀ x, V x ≤ W x) :
    wexp ψ V ≤ wexp ψ W :=
  Finset.sum_le_sum fun σ _ => integral_mono (hV σ) (hW σ) fun x =>
    mul_le_mul_of_nonneg_right (h x) (sq_nonneg _)

theorem wexp_nonneg {n : ℕ} (ψ : Wavefunction n) {W : Configuration n → ℝ} (h : ∀ x, 0 ≤ W x) :
    0 ≤ wexp ψ W :=
  Finset.sum_nonneg fun σ _ => integral_nonneg fun x => mul_nonneg (h x) (sq_nonneg _)

theorem wexp_one {n : ℕ} (ψ : Wavefunction n) : wexp ψ (fun _ => 1) = normSquared ψ := by
  simp [wexp, normSquared]

theorem integrable_bounded_weight {n : ℕ} {ψ : Wavefunction n} (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    {W : Configuration n → ℝ} (hW : Measurable W) {C : ℝ} (hb : ∀ x, |W x| ≤ C) (σ : Spins n) :
    Integrable (fun x => W x * ‖ψ σ x‖ ^ 2) :=
  integrable_supported_weight (hψ σ) hW (fun x _ => hb x)

/-- Multiplier identity for a minimizer. -/
theorem minimizer_multiplier_energy (Z : ℕ) {n : ℕ} {Φ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain Φ g) (hn : normSquared Φ = 1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n),
      FormDomain χ h → normSquared χ = 1 → energy Z Φ g ≤ energy Z χ h)
    {θ : Configuration n → ℝ} (hθ : SmoothMultiplier θ) :
    energy Z (multiplyWavefunction θ Φ) (multiplyGradient θ Φ g) =
      energy Z Φ g * wexp Φ (fun x => θ x ^ 2) + localizationError Φ θ := by
  have hsq : SmoothMultiplier (fun x => θ x ^ 2) := by
    simpa only [pow_two] using hθ.mul hθ
  rw [energy_localization_identity Z hd hθ, minimizer_multiplier_pairing Z hd hn hmin hsq]
  rfl

theorem normSquared_multiply {n : ℕ} (θ : Configuration n → ℝ) (Φ : Wavefunction n) :
    normSquared (multiplyWavefunction θ Φ) = wexp Φ (fun x => θ x ^ 2) := by
  simp only [normSquared, wexp, norm_multiplyWavefunction_sq]

theorem wexp_multiply {n : ℕ} (θ : Configuration n → ℝ) (Φ : Wavefunction n)
    (W : Configuration n → ℝ) :
    wexp (multiplyWavefunction θ Φ) W = wexp Φ (fun x => W x * θ x ^ 2) := by
  unfold wexp
  apply Finset.sum_congr rfl
  intro σ _
  apply integral_congr_ae
  filter_upwards [] with x
  rw [norm_multiplyWavefunction_sq]
  ring

/-- The insertion inequality at one center. -/
theorem insertion_inequality {N : ℕ} {Φ : Wavefunction N} {g : Gradient N}
    (hd : FormDomain Φ g) (hn : normSquared Φ = 1)
    (hmin : ∀ (χ : Wavefunction N) (h : Gradient N),
      FormDomain χ h → normSquared χ = 1 → energy (N + 1) Φ g ≤ energy (N + 1) χ h)
    {E' : ℝ} (hE' : ∀ (χ : Wavefunction (N + 1)) (h : Gradient (N + 1)),
      FormDomain χ h → normSquared χ = 1 → E' ≤ energy (N + 1) χ h)
    {y : Position} {b : ℝ} (hb : 0 < b) (hyb : b < ‖y‖) :
    (E' - energy (N + 1) Φ g) * wexp Φ (fun x => coreProduct y (2 * b) x ^ 2) ≤
      (1 / 2 : ℝ) * cutGradientConstant (2 * b) * wexp Φ (nearCount y (2 * b)) +
      (1 / 2 : ℝ) * (Coulomb.unitWindowKinetic / b ^ 2) *
        wexp Φ (fun x => coreProduct y (2 * b) x ^ 2) -
      wexp Φ (fun x => insertionField (N + 1) b y x * coreProduct y (2 * b) x ^ 2) := by
  have hr : 0 < 2 * b := by linarith
  set θ : Configuration N → ℝ := coreProduct y (2 * b) with hθdef
  have hθ : SmoothMultiplier θ := coreProduct_multiplier y hr
  set A := wexp Φ (fun x => θ x ^ 2) with hAdef
  set E := energy (N + 1) Φ g with hEdef
  have hdψ := hd.multiply hθ
  have hnψ : normSquared (multiplyWavefunction θ Φ) = A := normSquared_multiply θ Φ
  have hEψ := minimizer_multiplier_energy (N + 1) hd hn hmin hθ
  have hK0 : 0 ≤ cutGradientConstant (2 * b) := by unfold cutGradientConstant; positivity
  have hloc : localizationError Φ θ ≤
      (1 / 2 : ℝ) * cutGradientConstant (2 * b) * wexp Φ (nearCount y (2 * b)) := by
    apply localizationError_le_nearCount hd.2.2.1 hθ y (2 * b)
    intro x
    have h1 := coreProduct_gradient_bound y hr x
    have h2 : 0 ≤ cutGradientConstant (2 * b) * nearCount y (2 * b) x :=
      mul_nonneg hK0 (nearCount_nonneg _ _ _)
    have h3 : 0 ≤ coreProduct y (2 * b) x ^ 2 := sq_nonneg _
    nlinarith
  obtain ⟨C, hC⟩ := packetPotential_bounded hb
  have hC0 : 0 ≤ C := (packetPotential_nonneg b 0).trans (hC 0)
  have hHm : Measurable (insertionField (N + 1) b y (n := N)) := by
    unfold insertionField
    exact measurable_const.sub (Finset.measurable_sum _ fun i _ =>
      (packetPotential_measurable b).comp ((measurable_pi_apply i).sub measurable_const))
  have hHb : ∀ x : Configuration N, |insertionField (N + 1) b y x| ≤ (2 * N + 1) * C := by
    intro x
    unfold insertionField
    have hs0 : 0 ≤ ∑ i, packetPotential b (x i - y) :=
      Finset.sum_nonneg fun i _ => packetPotential_nonneg _ _
    have hs1 : ∑ i, packetPotential b (x i - y) ≤ N * C := by
      calc _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum fun i _ => hC _
        _ = N * C := by simp
    have hp0 := packetPotential_nonneg b (-y)
    have hp1 := hC (-y)
    rw [abs_le]
    push_cast
    constructor <;> nlinarith
  have hθm : Measurable θ := hθ.smooth.continuous.measurable
  have hθ01 : ∀ x, θ x ^ 2 ≤ 1 := fun x => by
    have h0 := coreProduct_nonneg (n := N) y (2 * b) x
    have h1 := coreProduct_le_one (n := N) y (2 * b) x
    nlinarith
  have hHθ : wexp Φ (fun x => insertionField (N + 1) b y x * θ x ^ 2) ≤ (2 * N + 1) * C * A := by
    rw [hAdef, ← wexp_const_mul]
    apply wexp_mono
    · exact integrable_bounded_weight hd.2.2.1 (hHm.mul (hθm.pow_const 2))
        (C := (2 * N + 1) * C) (fun x => by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (θ x))]
          have := hHb x
          have h0 : 0 ≤ (2 * (N : ℝ) + 1) * C := by positivity
          nlinarith [abs_nonneg (insertionField (N + 1) b y x), sq_nonneg (θ x), hθ01 x])
    · exact integrable_bounded_weight hd.2.2.1 (measurable_const.mul (hθm.pow_const 2))
        (C := (2 * N + 1) * C) (fun x => by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (θ x)), abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * (N : ℝ) + 1) * C)]
          have h0 : 0 ≤ (2 * (N : ℝ) + 1) * C := by positivity
          nlinarith [hθ01 x])
    · intro x
      have := (abs_le.mp (hHb x)).2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hA0 : 0 ≤ A := wexp_nonneg Φ (fun x => sq_nonneg (θ x))
  have hNy0 : 0 ≤ wexp Φ (nearCount y (2 * b)) := wexp_nonneg Φ (nearCount_nonneg _ _)
  rcases hA0.lt_or_eq with hA | hA
  · have hψs : ∀ σ x, multiplyWavefunction θ Φ σ x ≠ 0 → ∀ i, 2 * b ≤ ‖x i - y‖ := by
      intro σ x hx i
      have h0 : θ x ≠ 0 := by
        intro h0
        apply hx
        simp [multiplyWavefunction, h0]
      exact (coreProduct_support y hr h0 i).le
    have hgs : ∀ σ i a x, multiplyGradient θ Φ g σ i a x ≠ 0 → ∀ j, 2 * b ≤ ‖x j - y‖ := by
      intro σ i a x hx j
      by_cases h0 : θ x = 0
      · have h1 : fderiv ℝ θ x (coordinateDirection i a) ≠ 0 := by
          intro h1
          apply hx
          simp [multiplyGradient, h0, h1]
        exact coreProduct_fderiv_support y hr h1 j
      · exact (coreProduct_support y hr h0 j).le
    obtain ⟨χ, h, hdχ, hnχ, hen⟩ := ball_insertion (N + 1) hdψ hb hyb hψs hgs (hnψ ▸ hA)
    have h1 := hE' χ h hdχ hnχ
    rw [hnψ, hEψ] at hen
    have hw : (∑ σ, ∫ x, insertionField (N + 1) b y x * ‖multiplyWavefunction θ Φ σ x‖ ^ 2) =
        wexp Φ (fun x => insertionField (N + 1) b y x * θ x ^ 2) := wexp_multiply θ Φ _
    rw [hw, ← hAdef, ← hEdef] at hen
    have h2 : E' * A ≤ energy (N + 1) χ h * A := mul_le_mul_of_nonneg_right h1 hA.le
    push_cast at hen
    nlinarith
  · rw [← hA] at hHθ ⊢
    have hk : 0 ≤ (1 / 2 : ℝ) * cutGradientConstant (2 * b) * wexp Φ (nearCount y (2 * b)) := by
      positivity
    nlinarith

/-- Sum of the point potentials at `y` of the particles at distance at least `ρ` from `y`. -/
def farSum (y : Position) (ρ : ℝ) {n : ℕ} (x : Configuration n) : ℝ :=
  ∑ i, if x i ∈ {z : Position | ρ ≤ ‖z - y‖} then ‖x i - y‖⁻¹ else 0

theorem farSum_nonneg (y : Position) (ρ : ℝ) {n : ℕ} (x : Configuration n) : 0 ≤ farSum y ρ x :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> positivity

theorem farSum_le (y : Position) {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (x : Configuration n) :
    farSum y ρ x ≤ n / ρ := by
  unfold farSum
  calc _ ≤ ∑ _i : Fin n, ρ⁻¹ := Finset.sum_le_sum fun i _ => by
        split_ifs with h
        · exact inv_anti₀ hρ h
        · positivity
    _ = n / ρ := by simp [div_eq_mul_inv]

theorem farSum_measurable (y : Position) (ρ : ℝ) {n : ℕ} :
    Measurable (farSum y ρ (n := n)) := by
  unfold farSum
  refine Finset.measurable_sum _ fun i _ => Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_le measurable_const (measurable_norm.comp
      (measurable_id.sub measurable_const))).preimage (measurable_pi_apply i)
  · exact (measurable_norm.comp ((measurable_pi_apply i).sub measurable_const)).inv

theorem insertionField_le_far (Z : ℕ) {b ρ : ℝ} (hb : 0 < b) (hρ : b ≤ ρ) {y : Position}
    (hy : y ≠ 0) {n : ℕ} (x : Configuration n) :
    insertionField Z b y x ≤ (Z : ℝ) * ‖y‖⁻¹ - farSum y ρ x := by
  unfold insertionField farSum
  have h1 : (Z : ℝ) * packetPotential b (-y) ≤ (Z : ℝ) * ‖y‖⁻¹ := by
    have := packetPotential_le hb (neg_ne_zero.mpr hy)
    rw [norm_neg] at this
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have h2 : (∑ i, if x i ∈ {z : Position | ρ ≤ ‖z - y‖} then ‖x i - y‖⁻¹ else 0) ≤
      ∑ i, packetPotential b (x i - y) := Finset.sum_le_sum fun i _ => by
    split_ifs with h
    · exact (packetPotential_eq hb (hρ.trans h)).symm.le
    · exact packetPotential_nonneg _ _
  linarith

theorem wexp_farSum {n : ℕ} {ψ : Wavefunction n} (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (y : Position) {ρ : ℝ} (hρ : 0 < ρ) :
    wexp ψ (farSum y ρ) = farPotential ψ y ρ := by
  unfold wexp farPotential farSum
  apply Finset.sum_congr rfl
  intro σ _
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [] with x
    split_ifs <;> simp
  · intro i _
    refine integrable_bounded_weight hψ (W := fun x : Configuration n =>
      if x i ∈ {z : Position | ρ ≤ ‖z - y‖} then ‖x i - y‖⁻¹ else 0) ?_ (C := ρ⁻¹) ?_ σ
    · refine Measurable.ite ?_ ?_ measurable_const
      · exact (measurableSet_le measurable_const (measurable_norm.comp
          (measurable_id.sub measurable_const))).preimage (measurable_pi_apply i)
      · exact (measurable_norm.comp ((measurable_pi_apply i).sub measurable_const)).inv
    · intro x
      split_ifs with h
      · rw [abs_of_nonneg (by positivity)]
        exact inv_anti₀ hρ h
      · simp [hρ.le]

theorem sqrt_le_half_one_add {t : ℝ} (ht : 0 ≤ t) : Real.sqrt t ≤ (1 + t) / 2 := by
  nlinarith [Real.sq_sqrt ht, sq_nonneg (Real.sqrt t - 1)]

/-- The field lost on the configurations discarded by the core cut. -/
theorem loss_bound {N : ℕ} {Φ : Wavefunction N} {g : Gradient N}
    (hd : FormDomain Φ g) (hn : normSquared Φ = 1)
    (hmin : ∀ (χ : Wavefunction N) (h : Gradient N),
      FormDomain χ h → normSquared χ = 1 → energy (N + 1) Φ g ≤ energy (N + 1) χ h)
    {Eg D Cf P : ℝ} (hD : 0 ≤ D) (hCf : 0 ≤ Cf) (hP : 1 ≤ P) (hED : energy (N + 1) Φ g ≤ Eg + D)
    {y : Position} (hy : y ≠ 0)
    (hfield : ∀ {ψ : Wavefunction N} {h : Gradient N}, FormDomain ψ h → normSquared ψ = 1 →
      ∀ {δ : ℝ}, energy (N + 1) ψ h ≤ Eg + δ → 0 ≤ δ →
        ((N + 1 : ℕ) : ℝ) * ‖y‖⁻¹ - farPotential ψ y (40 * (‖y‖ / 100000)) ≤
          Cf * (Real.sqrt P * Coulomb.screenMass δ (‖y‖ / 100000) / (‖y‖ / 100000)))
    {b ε : ℝ} (hb : 0 < b) (hb40 : b ≤ 40 * (‖y‖ / 100000)) (ha1 : 1 ≤ ‖y‖ / 100000)
    (hε : 0 < ε) :
    wexp Φ (fun x => insertionField (N + 1) b y x * (1 - coreProduct y (2 * b) x ^ 2)) ≤
      Cf * Real.sqrt P * (
        (wexp Φ (fun x => 1 - coreProduct y (2 * b) x ^ 2) + ε) / (‖y‖ / 100000) +
        ((1 + D) * (wexp Φ (fun x => 1 - coreProduct y (2 * b) x ^ 2) + ε) +
          (1 / 2 : ℝ) * cutGradientConstant (2 * b) * wexp Φ (nearCount y (2 * b))) /
          (2 * Real.sqrt (‖y‖ / 100000))) +
      ε * N / (40 * (‖y‖ / 100000)) := by
  set a := ‖y‖ / 100000 with hadef
  have ha : 0 < a := by linarith
  have hr : 0 < 2 * b := by linarith
  have hρ : 0 < 40 * a := by positivity
  have hψ := hd.2.2.1
  set F : Configuration N → ℝ := coreProduct y (2 * b) with hFdef
  set θ : Configuration N → ℝ := lossMultiplier y (2 * b) ε with hθdef
  have hθ : SmoothMultiplier θ := lossMultiplier_multiplier y hr hε
  have hθsq : ∀ x, θ x ^ 2 = 1 + ε - F x ^ 2 := fun x => lossMultiplier_sq y (2 * b) hε.le x
  set p := wexp Φ (fun x => 1 - F x ^ 2) with hpdef
  set Ny := wexp Φ (nearCount y (2 * b)) with hNydef
  set K := cutGradientConstant (2 * b) with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; unfold cutGradientConstant; positivity
  have hFm : Measurable F := (coreProduct_multiplier (n := N) y hr).smooth.continuous.measurable
  have hF01 : ∀ x, 0 ≤ 1 - F x ^ 2 ∧ 1 - F x ^ 2 ≤ 1 := by
    intro x
    have h0 := coreProduct_nonneg (n := N) y (2 * b) x
    have h1 := coreProduct_le_one (n := N) y (2 * b) x
    constructor <;> nlinarith
  have hθm : Measurable θ := hθ.smooth.continuous.measurable
  have hint : ∀ {W : Configuration N → ℝ}, Measurable W → (∃ C, ∀ x, |W x| ≤ C) →
      ∀ σ, Integrable (fun x => W x * ‖Φ σ x‖ ^ 2) := by
    intro W hW hC σ
    obtain ⟨C, hC⟩ := hC
    exact integrable_bounded_weight hψ hW hC σ
  have hFb : ∃ C, ∀ x, |1 - F x ^ 2| ≤ C :=
    ⟨1, fun x => by rw [abs_of_nonneg (hF01 x).1]; exact (hF01 x).2⟩
  have hFsm : Measurable (fun x => 1 - F x ^ 2) := measurable_const.sub (hFm.pow_const 2)
  have hq : wexp Φ (fun x => θ x ^ 2) = p + ε := by
    have he : (fun x => θ x ^ 2) = fun x => (1 - F x ^ 2) + ε * 1 := by
      funext x; rw [hθsq]; ring
    rw [he, wexp_add hψ (hint hFsm hFb) (hint measurable_const ⟨|ε * 1|, fun _ => le_rfl⟩),
      wexp_const_mul, wexp_one, hn, mul_one]
  have hp0 : 0 ≤ p := wexp_nonneg Φ (fun x => (hF01 x).1)
  have hq0 : 0 < p + ε := by linarith
  have hloc : localizationError Φ θ ≤ (1 / 2 : ℝ) * K * Ny :=
    localizationError_le_nearCount hψ hθ y (2 * b) (fun x => lossMultiplier_gradient_bound y hr hε x)
  have hloc0 := localizationError_nonneg Φ θ
  set c := (Real.sqrt (p + ε))⁻¹ with hcdef
  have hc2 : c ^ 2 = (p + ε)⁻¹ := by rw [hcdef, inv_pow, Real.sq_sqrt hq0.le]
  have hdL := (hd.multiply hθ).scale c
  have hnL : normSquared (scaleWavefunction c (multiplyWavefunction θ Φ)) = 1 := by
    rw [normSquared_scale, normSquared_multiply, hq, hc2, inv_mul_cancel₀ hq0.ne']
  have heL : energy (N + 1) (scaleWavefunction c (multiplyWavefunction θ Φ))
      (scaleGradient c (multiplyGradient θ Φ g)) =
        energy (N + 1) Φ g + localizationError Φ θ / (p + ε) := by
    rw [energy_scale, minimizer_multiplier_energy (N + 1) hd hn hmin hθ, hq, hc2]
    field_simp
  set δ := D + localizationError Φ θ / (p + ε) with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hfL := hfield hdL hnL (δ := δ) (by rw [heL]; linarith) hδ0
  have hfarL : farPotential (scaleWavefunction c (multiplyWavefunction θ Φ)) y (40 * a) =
      c ^ 2 * wexp Φ (fun x => farSum y (40 * a) x * θ x ^ 2) := by
    rw [← wexp_farSum hdL.2.2.1 y hρ]
    unfold wexp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [scaleWavefunction, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      norm_multiplyWavefunction_sq]
    ring
  have hfsm : Measurable (farSum y (40 * a) (n := N)) := farSum_measurable y _
  have hfsb : ∀ x : Configuration N, |farSum y (40 * a) x| ≤ N / (40 * a) := fun x => by
    rw [abs_of_nonneg (farSum_nonneg _ _ _)]; exact farSum_le y hρ x
  have hθb : ∀ x, |θ x ^ 2| ≤ 1 + ε := fun x => by
    rw [abs_of_nonneg (sq_nonneg _), hθsq]; linarith [(hF01 x).1, (hF01 x).2]
  -- the expected far field in the loss state
  set Y := ((N + 1 : ℕ) : ℝ) * ‖y‖⁻¹ with hYdef
  have hY0 : 0 ≤ Y := by positivity
  have hfθ : wexp Φ (fun x => (Y - farSum y (40 * a) x) * θ x ^ 2) =
      (p + ε) * (Y - farPotential (scaleWavefunction c (multiplyWavefunction θ Φ)) y (40 * a)) := by
    have he : (fun x => (Y - farSum y (40 * a) x) * θ x ^ 2) =
        fun x => Y * θ x ^ 2 + (-1) * (farSum y (40 * a) x * θ x ^ 2) := by
      funext x; ring
    rw [he, wexp_add hψ (hint (W := fun x => Y * θ x ^ 2) (measurable_const.mul (hθm.pow_const 2))
        ⟨|Y| * (1 + ε), fun x => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hθb x) (abs_nonneg _)⟩)
      (hint (W := fun x => (-1) * (farSum y (40 * a) x * θ x ^ 2))
        (measurable_const.mul (hfsm.mul (hθm.pow_const 2)))
        ⟨1 * (N / (40 * a) * (1 + ε)), fun x => by
          rw [abs_mul, abs_mul]
          simp only [abs_neg, abs_one]
          exact mul_le_mul_of_nonneg_left (mul_le_mul (hfsb x) (hθb x) (abs_nonneg _) (by positivity))
            zero_le_one⟩)]
    rw [wexp_const_mul, wexp_const_mul, hq, hfarL, hc2]
    field_simp
    ring
  -- pointwise comparison with the far field
  have hHle : ∀ x : Configuration N, insertionField (N + 1) b y x ≤ Y - farSum y (40 * a) x :=
    fun x => insertionField_le_far (N + 1) hb hb40 hy x
  obtain ⟨CU, hCU⟩ := packetPotential_bounded hb
  have hCU0 : 0 ≤ CU := (packetPotential_nonneg b 0).trans (hCU 0)
  have hHm : Measurable (insertionField (N + 1) b y (n := N)) := by
    unfold insertionField
    exact measurable_const.sub (Finset.measurable_sum _ fun i _ =>
      (packetPotential_measurable b).comp ((measurable_pi_apply i).sub measurable_const))
  have hHb : ∀ x : Configuration N, |insertionField (N + 1) b y x| ≤ (2 * N + 1) * CU := by
    intro x
    unfold insertionField
    have hs0 : 0 ≤ ∑ i, packetPotential b (x i - y) :=
      Finset.sum_nonneg fun i _ => packetPotential_nonneg _ _
    have hs1 : ∑ i, packetPotential b (x i - y) ≤ N * CU := by
      calc _ ≤ ∑ _i : Fin N, CU := Finset.sum_le_sum fun i _ => hCU _
        _ = N * CU := by simp
    have hp0 := packetPotential_nonneg b (-y)
    have hp1 := hCU (-y)
    rw [abs_le]
    push_cast
    constructor <;> nlinarith
  have hJb : ∀ x : Configuration N, |Y - farSum y (40 * a) x| ≤ Y + N / (40 * a) := fun x => by
    have := hfsb x
    rw [abs_le] at this ⊢
    constructor <;> linarith [farSum_nonneg y (40 * a) x]
  have hstep1 : wexp Φ (fun x => insertionField (N + 1) b y x * (1 - F x ^ 2)) ≤
      wexp Φ (fun x => (Y - farSum y (40 * a) x) * (1 - F x ^ 2)) := by
    apply wexp_mono
    · exact hint (W := fun x => insertionField (N + 1) b y x * (1 - F x ^ 2)) (hHm.mul hFsm)
        ⟨(2 * N + 1) * CU * 1, fun x => by
          rw [abs_mul, abs_of_nonneg (hF01 x).1]
          exact mul_le_mul (hHb x) (hF01 x).2 (hF01 x).1 (by positivity)⟩
    · exact hint (W := fun x => (Y - farSum y (40 * a) x) * (1 - F x ^ 2))
        ((measurable_const.sub hfsm).mul hFsm) ⟨(Y + N / (40 * a)) * 1, fun x => by
        rw [abs_mul, abs_of_nonneg (hF01 x).1]
        exact mul_le_mul (hJb x) (hF01 x).2 (hF01 x).1 (by positivity)⟩
    · intro x
      exact mul_le_mul_of_nonneg_right (hHle x) (hF01 x).1
  have hJm : Measurable (fun x : Configuration N => Y - farSum y (40 * a) x) :=
    measurable_const.sub hfsm
  have hsplit : wexp Φ (fun x => (Y - farSum y (40 * a) x) * (1 - F x ^ 2)) =
      wexp Φ (fun x => (Y - farSum y (40 * a) x) * θ x ^ 2) +
        (-ε) * wexp Φ (fun x => Y - farSum y (40 * a) x) := by
    have he : (fun x => (Y - farSum y (40 * a) x) * (1 - F x ^ 2)) =
        fun x => (Y - farSum y (40 * a) x) * θ x ^ 2 + (-ε) * (Y - farSum y (40 * a) x) := by
      funext x; rw [hθsq]; ring
    rw [he, wexp_add hψ (hint (W := fun x => (Y - farSum y (40 * a) x) * θ x ^ 2)
        (hJm.mul (hθm.pow_const 2)) ⟨(Y + N / (40 * a)) * (1 + ε), fun x => by
          rw [abs_mul]; exact mul_le_mul (hJb x) (hθb x) (abs_nonneg _) (by positivity)⟩)
      (hint (W := fun x => (-ε) * (Y - farSum y (40 * a) x)) (measurable_const.mul hJm)
        ⟨|-ε| * (Y + N / (40 * a)), fun x => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hJb x) (abs_nonneg _)⟩),
      wexp_const_mul]
  have hJlow : -(N / (40 * a)) ≤ wexp Φ (fun x => Y - farSum y (40 * a) x) := by
    have h := wexp_mono (ψ := Φ) (V := fun _ => (-(N / (40 * a))) * 1)
      (W := fun x => Y - farSum y (40 * a) x)
      (hint measurable_const ⟨|(-(N / (40 * a))) * 1|, fun _ => le_rfl⟩)
      (hint hJm ⟨Y + N / (40 * a), hJb⟩)
      (fun x => by linarith [farSum_le y hρ x])
    rwa [wexp_const_mul, wexp_one, hn, mul_one] at h
  have hfield' : (p + ε) * (Y - farPotential (scaleWavefunction c (multiplyWavefunction θ Φ)) y
      (40 * a)) ≤ (p + ε) * (Cf * (Real.sqrt P * Coulomb.screenMass δ a / a)) :=
    mul_le_mul_of_nonneg_left hfL hq0.le
  -- the algebra of the screening unit
  set sa := Real.sqrt a with hsadef
  have hsa : 0 < sa := Real.sqrt_pos.mpr ha
  have hsa2 : sa * sa = a := Real.mul_self_sqrt ha.le
  have hbase : Coulomb.screenBaseMass a = 1 := by
    unfold Coulomb.screenBaseMass
    exact max_eq_right (inv_le_one_of_one_le₀ (one_le_pow₀ ha1))
  have hsδ : Real.sqrt δ ≤ (1 + δ) / 2 := by
    exact sqrt_le_half_one_add hδ0
  have hsδa : Real.sqrt (δ * a) ≤ (1 + δ) / 2 * sa := by
    rw [Real.sqrt_mul hδ0]
    exact mul_le_mul_of_nonneg_right hsδ hsa.le
  have hqδ : (p + ε) * (1 + δ) ≤ (1 + D) * (p + ε) + (1 / 2 : ℝ) * K * Ny := by
    have : (p + ε) * (1 + δ) = (1 + D) * (p + ε) + localizationError Φ θ := by
      rw [hδdef]; field_simp; ring
    linarith
  have hkey : (p + ε) * Coulomb.screenMass δ a / a ≤
      (p + ε) / a + ((1 + D) * (p + ε) + (1 / 2 : ℝ) * K * Ny) / (2 * sa) := by
    unfold Coulomb.screenMass
    rw [hbase]
    have h1 : (p + ε) * Real.sqrt (δ * a) / a ≤ (p + ε) * (1 + δ) / (2 * sa) := by
      calc (p + ε) * Real.sqrt (δ * a) / a ≤ (p + ε) * ((1 + δ) / 2 * sa) / a :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsδa hq0.le) ha.le
        _ = (p + ε) * (1 + δ) / (2 * sa) := by
            rw [← hsa2]; field_simp
    have h2 : (p + ε) * (1 + δ) / (2 * sa) ≤
        ((1 + D) * (p + ε) + (1 / 2 : ℝ) * K * Ny) / (2 * sa) :=
      div_le_div_of_nonneg_right hqδ (by positivity)
    have h3 : (p + ε) * (1 + Real.sqrt (δ * a)) / a =
        (p + ε) / a + (p + ε) * Real.sqrt (δ * a) / a := by ring
    linarith
  have hsP : 0 ≤ Cf * Real.sqrt P := mul_nonneg hCf (Real.sqrt_nonneg _)
  have hfinal : (p + ε) * (Cf * (Real.sqrt P * Coulomb.screenMass δ a / a)) ≤
      Cf * Real.sqrt P * ((p + ε) / a +
        ((1 + D) * (p + ε) + (1 / 2 : ℝ) * K * Ny) / (2 * sa)) := by
    have he : (p + ε) * (Cf * (Real.sqrt P * Coulomb.screenMass δ a / a)) =
        Cf * Real.sqrt P * ((p + ε) * Coulomb.screenMass δ a / a) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hkey hsP
  have hεN : -ε * wexp Φ (fun x => Y - farSum y (40 * a) x) ≤ ε * N / (40 * a) := by
    have := mul_le_mul_of_nonneg_left hJlow hε.le
    have he : ε * (-(N / (40 * a))) = -(ε * N / (40 * a)) := by ring
    linarith
  calc wexp Φ (fun x => insertionField (N + 1) b y x * (1 - coreProduct y (2 * b) x ^ 2))
      ≤ wexp Φ (fun x => (Y - farSum y (40 * a) x) * (1 - F x ^ 2)) := hstep1
    _ = (p + ε) * (Y - farPotential (scaleWavefunction c (multiplyWavefunction θ Φ)) y (40 * a)) +
        (-ε) * wexp Φ (fun x => Y - farSum y (40 * a) x) := by rw [hsplit, hfθ]
    _ ≤ _ := by linarith

end

end AtomicIonization.IonizationGap
