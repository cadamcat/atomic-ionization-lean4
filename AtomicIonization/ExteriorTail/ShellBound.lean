import AtomicIonization.ExteriorTail.BiasedState
import AtomicIonization.ExteriorTail.BiasedEnvelope
import AtomicIonization.ExteriorTail.BiasedSlice
import AtomicIonization.ExteriorTail.WeightedGap
import AtomicIonization.ExteriorTail.TailAlgebra

/-!
# The shell estimate

For an atomic ground state with energy offset at most `D` above the unrestricted bottom and an
ionization gap at least `c > 0`, the expected shell occupation `𝔼 ∑ᵢ χ_r(xᵢ)²` is at most `K / r`
for all `r ≥ r₁`, with `K, r₁` depending only on `D` and `c`.
-/

namespace AtomicIonization.ExteriorTail

open OAI Coulomb MeasureTheory
open scoped ContDiff

noncomputable section

theorem shellBump_grad_le {r : ℝ} (hr : 0 < r) {n : ℕ} (x : Configuration n) :
    ∑ i, ∑ b : Fin 3, (fderiv ℝ (shellBump r) (position x i) (EuclideanSpace.single b 1)) ^ 2 ≤
      3 * (shellLip / r) ^ 2 * localCount (imsShell 0 r) x := by
  unfold localCount
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : position x i ∈ imsShell 0 r
  · rw [Set.indicator_of_mem hi, mul_one]
    calc
      _ ≤ ∑ _b : Fin 3, (shellLip / r) ^ 2 := Finset.sum_le_sum fun b _ => by
        have h := shellBump_deriv_le hr b (position x i)
        have h2 := (sq_le_sq₀ (abs_nonneg _) (div_nonneg shellLip_nonneg hr.le)).mpr h
        rwa [sq_abs] at h2
      _ = _ := by simp
  · rw [Set.indicator_of_notMem hi, mul_zero]
    simp [fderiv_shellBump_eq_zero hr hi]

theorem shellBump_sq_vanish {r : ℝ} (hr : 0 < r) (y : Space) (hy : y ∉ imsShell 0 r) :
    shellBump r y ^ 2 = 0 := by
  have h : ‖y‖ ≤ r ∨ 2 * r ≤ ‖y‖ := by
    simp only [imsShell, Set.mem_ofPred_eq, sub_zero, not_and_or, not_le] at hy
    rcases hy with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  rw [shellBump_eq_zero hr h]; ring

theorem shell_mass_bound {D c : ℝ} (hD : 0 ≤ D) (hc : 0 < c) :
    ∃ K r₁ : ℝ, 0 ≤ K ∧ 1 ≤ r₁ ∧
    ∀ (Z : ℕ) (hZ : 1 ≤ Z) {n : ℕ}, 1 ≤ n → ∀ (u : H1Vector n), Antisymmetric u → mass u = 1 →
      (form (atom Z hZ) u : EReal) = sectorFormBottom (atom Z hZ) n →
      ∀ {E P : ℝ}, (E : EReal) ≤ unrestrictedFormBottom (atom Z hZ) →
        form (atom Z hZ) u ≤ E + D →
        (P : EReal) ≤ sectorFormBottom (atom Z hZ) (n - 1) → c ≤ P - form (atom Z hZ) u →
        ∀ r : ℝ, r₁ ≤ r → potentialForm (shellCount r) u ≤ K / r := by
  obtain ⟨CE, hCE, HE⟩ := biased_shell_envelope
  obtain ⟨CA, hCA, HA⟩ := atomic_annular_second_moment (α := 1 / 2) (β := 3)
    (by norm_num) (by norm_num)
  refine ⟨tailConstant c CE shellLip CA D, tailRadius c CE D, tailConstant_nonneg hc,
    le_max_left _ _, ?_⟩
  intro Z hZ n hn u ha hm hmin E P hE hoff hP hgap r hr
  set S := atom Z hZ
  have hatom : ∀ j, S.position j = 0 := fun _ => rfl
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 < r := by linarith
  set L := shellLip
  set m := potentialForm (shellCount r) u with hmdef
  set N := expectedPopulation u (imsShell 0 r) with hNdef
  have hA : MeasurableSet (imsShell (0 : Space) r) := measurableSet_imsShell 0 r
  have hloc : Measurable (localCount (n := n) (imsShell 0 r)) := localCount_measurable hA
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun s _ => integral_nonneg fun x =>
    mul_nonneg (shellCount_nonneg r x) (sq_nonneg _)
  have hN0 : 0 ≤ N := expectedPopulation_nonneg _ _
  -- the shell population in the original state
  have hscreen : screenMass D r = 1 + Real.sqrt (D * r) := by
    unfold screenMass screenBaseMass
    rw [max_eq_right]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hr1)
  have hN : N ≤ Real.sqrt CA * (1 + Real.sqrt D) * Real.sqrt r := by
    have hB : MeasurableSet {x : Space | 1 / 2 * r < ‖x‖ ∧ ‖x‖ < 3 * r} :=
      ((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)).measurableSet
    have hsub : imsShell (0 : Space) r ⊆ {x : Space | 1 / 2 * r < ‖x‖ ∧ ‖x‖ < 3 * r} := by
      intro x hx
      simp only [imsShell, Set.mem_ofPred_eq, sub_zero] at hx
      constructor <;> linarith [hx.1, hx.2]
    have h2 := (expectedPopulation_sq_le u hA hm).trans
      ((localCountSecondMoment_mono u hB hsub).trans (HA S hatom u ha hm hE hoff hD hr0))
    rw [hscreen] at h2
    have h3 : N ≤ Real.sqrt CA * (1 + Real.sqrt (D * r)) := by
      have := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq hN0, Real.sqrt_mul hCA, Real.sqrt_sq (by positivity)] at this
    have hsr : 1 ≤ Real.sqrt r := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hr1
    have h4 : 1 + Real.sqrt (D * r) ≤ (1 + Real.sqrt D) * Real.sqrt r := by
      rw [Real.sqrt_mul hD]; nlinarith [Real.sqrt_nonneg D]
    calc N ≤ _ := h3
      _ ≤ Real.sqrt CA * ((1 + Real.sqrt D) * Real.sqrt r) :=
        mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
      _ = _ := by ring
  -- the weighted eigen-inequality
  set w : Space → ℝ := fun y => (shellBump r y) ^ 2
  set W := weightedInnerField S (r / 8) w
  have HG := weighted_gap_inequality Z hZ hn u ha hm hmin hP (shellCoeff hr0) (r / 8)
  change (P - form S u) * m ≤ (1 / 2 : ℝ) * potentialForm (fun x => ∑ i, ∑ b : Fin 3,
      (fderiv ℝ (shellBump r) (position x i) (EuclideanSpace.single b 1)) ^ 2) u +
    potentialForm W u at HG
  have hgrad : potentialForm (fun x => ∑ i, ∑ b : Fin 3,
      (fderiv ℝ (shellBump r) (position x i) (EuclideanSpace.single b 1)) ^ 2) u ≤
      3 * (L / r) ^ 2 * N := by
    have hcont : ∀ (i : Fin n) (b : Fin 3), Continuous (fun x : Configuration n =>
        fderiv ℝ (shellBump r) (position x i) (EuclideanSpace.single b 1)) := fun i b =>
      (((shellBump_contDiff r).continuous_fderiv (by simp)).clm_apply continuous_const).comp
        (continuous_position i)
    have hmeas : Measurable (fun x : Configuration n => ∑ i, ∑ b : Fin 3,
        (fderiv ℝ (shellBump r) (position x i) (EuclideanSpace.single b 1)) ^ 2) :=
      Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun b _ =>
        (hcont i b).measurable.pow_const 2
    have hmono := potentialForm_mono_ae u _ (fun x => 3 * (L / r) ^ 2 * localCount (imsShell 0 r) x)
      (fun s => boundedObservable_integrable u _ hmeas (B := 3 * (L / r) ^ 2 * n) (fun x => by
        have h0 : 0 ≤ ∑ i, ∑ b : Fin 3,
            (fderiv ℝ (shellBump r) (position x i) (EuclideanSpace.single b 1)) ^ 2 :=
          Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
        rw [abs_of_nonneg h0]
        exact (shellBump_grad_le hr0 x).trans
          (mul_le_mul_of_nonneg_left (localCount_le _ _) (by positivity))) s)
      (fun s => boundedObservable_integrable u _ (measurable_const.mul hloc)
        (B := 3 * (L / r) ^ 2 * n) (fun x => by
          change |3 * (L / r) ^ 2 * localCount (imsShell 0 r) x| ≤ _
          rw [abs_of_nonneg (mul_nonneg (by positivity) (localCount_nonneg _ _))]
          exact mul_le_mul_of_nonneg_left (localCount_le _ _) (by positivity)) s)
      (Filter.Eventually.of_forall fun x => shellBump_grad_le hr0 x)
    have hpop : potentialForm (fun x => 3 * (L / r) ^ 2 * localCount (imsShell 0 r) x) u =
        3 * (L / r) ^ 2 * N := by
      rw [hNdef, expectedPopulation_eq u hA]
      simp only [potentialForm, mul_assoc, integral_const_mul, ← Finset.mul_sum]
    linarith
  -- trivial case
  rcases hm0.eq_or_lt with hzero | hpos
  · rw [← hzero]; exact div_nonneg (tailConstant_nonneg hc) hr0.le
  -- the biased state
  have hn0 : n ≠ 0 := by omega
  have hground := groundState_of_min Z hZ hn0 u ha hm hmin
  set φ₀ := biasMul u hr0 hpos
  have hmass₀ : mass φ₀ = 2 * m := by
    rw [mass_biasMul, hm]; ring
  have hmass₀pos : 0 < mass φ₀ := by rw [hmass₀]; linarith
  set G := (1 / 2 : ℝ) * ∑ s, ∑ a, ∫ x,
    (fderiv ℝ (shellRoot r m (n := n)) x (EuclideanSpace.single a 1)) ^ 2 * ‖u.value s x‖ ^ 2
  have hG : G ≤ 3 / 2 * (L / r) ^ 2 * N := by
    exact biasMul_gradient_le u hr0 hpos
  have hG0 : 0 ≤ G := by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hform₀ := form_biasMul hn0 hground hr0 hpos
  set φ := φ₀.normalized
  have hφa : Antisymmetric φ :=
    (u.smoothMul_antisymmetric ha _ _ _ _ _ _ (shellRoot_permute r m)).normalized
  have hφm : mass φ = 1 := mass_normalized φ₀ hmass₀pos
  have hφform : form S φ = form S u + G / (2 * m) := by
    have h : mass φ₀ * form S φ = form S φ₀ := form_normalized_weight S φ₀
    rw [hform₀, hmass₀] at h
    have h2m : (2 * m) ≠ 0 := by positivity
    calc form S φ = (2 * m * form S φ) / (2 * m) := by field_simp
      _ = (form S u * (2 * m) + G) / (2 * m) := by rw [h]
      _ = form S u + G / (2 * m) := by field_simp
  set δ := D + G / (2 * m)
  have hδ : 0 ≤ δ := by positivity
  have hφoff : form S φ ≤ E + δ := by rw [hφform]; simp only [δ]; linarith
  obtain ⟨T, hTc, hTf, _, hTcs, hTos, hTm, hTe⟩ := exists_annular_recorded_ensemble S φ hφa hr0
  obtain ⟨M, hM⟩ := HE S hatom φ hφa hφm hE hφoff hδ hr0 T hTc hTf hTos hTm hTe
  have hw0 : ∀ y, 0 ≤ w y := fun y => sq_nonneg _
  have hw1 : ∀ y, w y ≤ 1 := fun y => by
    have h0 := shellBump_nonneg r y
    have h1 := shellBump_le_one r y
    simp only [w]; nlinarith
  have hws : ∀ y ∉ imsShell 0 r, w y = 0 := fun y hy => shellBump_sq_vanish hr0 y hy
  have hwm : Measurable w := (measurable_shellBump r).pow_const 2
  have HS := normalized_weighted_inner_le S hatom hTc (hTm.trans hφm) hr0
    (show r / 8 ≤ r / 2 by linarith) hwm hw0 hw1 hws hTcs M hpos
  -- change of law
  set W' : Configuration n → ℝ := fun x => W x / (m + ∑ i, w (position x i))
  have hlaw : potentialForm W u = 2 * m * potentialForm W' φ := by
    have h1 : potentialForm W u = potentialForm (fun x => W' x * (m + shellCount r x)) u := by
      unfold potentialForm
      apply Finset.sum_congr rfl
      intro s _
      apply integral_congr_ae
      filter_upwards [] with x
      have hpos' : 0 < m + shellCount r x := by linarith [shellCount_nonneg r x]
      simp only [W', w, shellCount] at hpos' ⊢
      field_simp
    rw [h1, ← potentialForm_biasMul u hr0 hpos, ← potentialForm_normalized_weight W' φ₀, hmass₀]
  have hW : potentialForm W u ≤ 2 * m * (CE * screenMass δ r / r) := by
    rw [hlaw]
    exact mul_le_mul_of_nonneg_left (HS.trans hM) (by positivity)
  -- assemble
  have hsδ : Real.sqrt (δ * r) ≤ Real.sqrt (D * r) + Real.sqrt (G * r / (2 * m)) := by
    have : δ * r = D * r + G * r / (2 * m) := by simp only [δ]; ring
    rw [this]
    exact sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)
  have hscreenδ : screenMass δ r ≤ 1 + Real.sqrt (D * r) + Real.sqrt (G * r / (2 * m)) := by
    unfold screenMass screenBaseMass
    rw [max_eq_right (inv_le_one_of_one_le₀ (one_le_pow₀ hr1))]
    linarith
  have hmain : c * m ≤ 3 / 2 * (L / r) ^ 2 * N +
      2 * m * CE * (1 + Real.sqrt (D * r) + Real.sqrt (G * r / (2 * m))) / r := by
    have h1 : c * m ≤ (P - form S u) * m := mul_le_mul_of_nonneg_right hgap hm0
    have h2 : 2 * m * (CE * screenMass δ r / r) ≤
        2 * m * CE * (1 + Real.sqrt (D * r) + Real.sqrt (G * r / (2 * m))) / r := by
      rw [show 2 * m * (CE * screenMass δ r / r) = 2 * m * CE * screenMass δ r / r by ring]
      apply div_le_div_of_nonneg_right _ hr0.le
      exact mul_le_mul_of_nonneg_left hscreenδ (by positivity)
    linarith
  exact tail_algebra hc hCE hD hr hpos hG0 hG hN hmain

end

end AtomicIonization.ExteriorTail
