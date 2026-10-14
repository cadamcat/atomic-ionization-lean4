import AtomicIonization.IonizationGap.PerCenter
import AtomicIonization.IonizationGap.Shell
import OAI.Analysis.CoulombRadii.FieldAnalysis.NewtonSubmean

/-!
# Averaging the insertion center over a shell

The insertion center `y` is averaged with the uniform density of the shell `{S ≤ |y| < 2S}`.
* Fubini exchanges the average with the expectation in a fixed state.
* For every configuration of `N` electrons, the averaged packet field of the nucleus of charge
  `N + 1` and of the electrons is at least the shell moment: the nucleus contributes its full
  charge, and by Newton's theorem each electron contributes at most one unit.
* The averaged number of electrons near the center is at most the volume of the near ball times
  the number of electrons in the annulus `S/2 < |x| < 3S`.
-/

namespace AtomicIonization.IonizationGap

open OAI OAI.NeutralAtom MeasureTheory

noncomputable section

/-- Fubini for the shell average of a bounded jointly measurable observable. -/
theorem average_wexp {n : ℕ} {Φ : Wavefunction n} (hΦ : ∀ σ, MemLp (Φ σ) 2 volume)
    {ρ : Position → ℝ} (hρ : Integrable ρ) (hρm : Measurable ρ)
    {W : Position → Configuration n → ℝ} (hW : Measurable (Function.uncurry W)) {C : ℝ}
    (hC : ∀ y x, |W y x| ≤ C) :
    Integrable (fun y => ρ y * wexp Φ (W y)) ∧
      (∫ y, ρ y * wexp Φ (W y)) = wexp Φ (fun x => ∫ y, ρ y * W y x) ∧
      ∀ σ, Integrable (fun x => (∫ y, ρ y * W y x) * ‖Φ σ x‖ ^ 2) := by
  have hprod : ∀ σ, Integrable (fun z : Position × Configuration n =>
      ρ z.1 * W z.1 z.2 * ‖Φ σ z.2‖ ^ 2) (volume.prod volume) := by
    intro σ
    have hdom : Integrable (fun z : Position × Configuration n => ρ z.1 * (C * ‖Φ σ z.2‖ ^ 2))
        (volume.prod volume) := hρ.mul_prod ((hΦ σ).norm.integrable_sq.const_mul C)
    refine hdom.norm.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact ((hρm.comp measurable_fst).mul hW).aestronglyMeasurable.mul
        ((hΦ σ).aestronglyMeasurable.norm.pow 2).comp_snd
    · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (sq_nonneg ‖Φ σ z.2‖)]
      have h1 := hC z.1 z.2
      have h2 : 0 ≤ |ρ z.1| := abs_nonneg _
      have h3 : 0 ≤ ‖Φ σ z.2‖ ^ 2 := sq_nonneg _
      calc |ρ z.1| * |W z.1 z.2| * ‖Φ σ z.2‖ ^ 2 ≤ |ρ z.1| * |C| * ‖Φ σ z.2‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (h1.trans (le_abs_self C)) h2) h3
        _ = _ := by ring
  have heq : (fun y => ρ y * wexp Φ (W y)) =
      fun y => ∑ σ, ∫ x, ρ y * W y x * ‖Φ σ x‖ ^ 2 := by
    funext y
    unfold wexp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact integrable_finsetSum _ fun σ _ => (hprod σ).integral_prod_left
  · rw [heq, integral_finsetSum _ fun σ _ => (hprod σ).integral_prod_left]
    unfold wexp
    apply Finset.sum_congr rfl
    intro σ _
    have hs := integral_integral_swap (μ := (volume : Measure Position))
      (ν := (volume : Measure (Configuration n)))
      (f := fun y x => ρ y * W y x * ‖Φ σ x‖ ^ 2) (hprod σ)
    rw [hs]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [← integral_mul_const]
  · intro σ
    refine (hprod σ).integral_prod_right.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← integral_mul_const]

theorem insertionField_measurable (Z : ℕ) (b : ℝ) {n : ℕ} :
    Measurable (Function.uncurry (fun y (x : Configuration n) => insertionField Z b y x)) := by
  unfold insertionField
  refine (measurable_const.mul ((packetPotential_measurable b).comp measurable_fst.neg)).sub
    (Finset.measurable_sum _ fun i _ => (packetPotential_measurable b).comp
      (((measurable_pi_apply i).comp measurable_snd).sub measurable_fst))

theorem insertionField_abs_le (Z : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, ∀ y {n : ℕ} (x : Configuration n), |insertionField Z b y x| ≤ (Z + n) * C := by
  obtain ⟨C, hC⟩ := packetPotential_bounded hb
  refine ⟨C, fun y n x => ?_⟩
  have hC0 : 0 ≤ C := (packetPotential_nonneg b 0).trans (hC 0)
  unfold insertionField
  have hs0 : 0 ≤ ∑ i, packetPotential b (x i - y) :=
    Finset.sum_nonneg fun i _ => packetPotential_nonneg _ _
  have hs1 : ∑ i, packetPotential b (x i - y) ≤ n * C := by
    calc _ ≤ ∑ _i : Fin n, C := Finset.sum_le_sum fun i _ => hC _
      _ = n * C := by simp
  have hp0 := packetPotential_nonneg b (-y)
  have hp1 := hC (-y)
  rw [abs_le]
  constructor <;> nlinarith

theorem nearCount_measurable (r : ℝ) {n : ℕ} :
    Measurable (Function.uncurry (fun y (x : Configuration n) => nearCount y r x)) := by
  unfold nearCount
  refine Finset.measurable_sum _ fun i _ => ?_
  have he : (fun z : Position × Configuration n =>
      (Metric.closedBall z.1 (2 * r)).indicator (fun _ => (1 : ℝ)) (z.2 i)) =
      fun z => if ‖z.2 i - z.1‖ ≤ 2 * r then (1 : ℝ) else 0 := by
    funext z
    by_cases h : ‖z.2 i - z.1‖ ≤ 2 * r <;>
      simp [Set.indicator_apply, Metric.mem_closedBall, dist_eq_norm, h]
  change Measurable (fun z : Position × Configuration n =>
      (Metric.closedBall z.1 (2 * r)).indicator (fun _ => (1 : ℝ)) (z.2 i))
  rw [he]
  have hm : Measurable fun z : Position × Configuration n => ‖z.2 i - z.1‖ := by fun_prop
  exact Measurable.ite (measurableSet_le hm measurable_const) measurable_const measurable_const

/-- The shell average of the packet field is at least the shell moment. -/
theorem shell_average_field {S b : ℝ} (hS : 0 < S) (hb : 0 < b) (hbS : b ≤ S) {N : ℕ}
    (x : Configuration N) :
    Coulomb.radialShellMoment S ≤
      ∫ y, Coulomb.radialShellDensity S y * insertionField (N + 1) b y x := by
  set ρ := Coulomb.radialShellDensity S with hρdef
  have hρi : Integrable ρ := Coulomb.radialShellDensity_integrable S
  have hρm : Measurable ρ := Coulomb.radialShellDensity_measurable S
  have hρ0 : ∀ y, 0 ≤ ρ y := Coulomb.radialShellDensity_nonneg S
  obtain ⟨C, hC⟩ := packetPotential_bounded hb
  have hU0 := packetPotential_nonneg b
  have hint : ∀ f : Position → Position, Measurable f →
      Integrable (fun y => ρ y * packetPotential b (f y)) := by
    intro f hf
    refine (hρi.mul_const C).mono' (hρm.mul ((packetPotential_measurable b).comp hf)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 y), abs_of_nonneg (hU0 _)]
    exact mul_le_mul_of_nonneg_left (hC _) (hρ0 y)
  have he : (fun y => ρ y * insertionField (N + 1) b y x) = fun y =>
      ((N + 1 : ℕ) : ℝ) * (ρ y * packetPotential b (-y)) -
        ∑ i, ρ y * packetPotential b (x i - y) := by
    funext y
    simp only [insertionField, mul_sub, Finset.mul_sum]
    ring
  have hIe : ∀ i, Integrable (fun y => ρ y * packetPotential b (x i - y)) := fun i =>
    hint (fun y => x i - y) (measurable_const.sub measurable_id)
  have hI1 : Integrable (fun y => ((N + 1 : ℕ) : ℝ) * (ρ y * packetPotential b (-y))) :=
    (hint (fun y => -y) measurable_neg).const_mul _
  have hI2 : Integrable (fun y => ∑ i, ρ y * packetPotential b (x i - y)) :=
    integrable_finsetSum _ fun i _ => hIe i
  rw [he, integral_sub hI1 hI2, integral_const_mul, integral_finsetSum _ fun i _ => hIe i]
  have hnuc : (∫ y, ρ y * packetPotential b (-y)) = Coulomb.radialShellMoment S := by
    unfold Coulomb.radialShellMoment
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : ρ y = 0
    · have hy' : Coulomb.radialShellDensity S y = 0 := hy
      rw [hy, hy']
      simp
    · have hyS : S ≤ ‖y‖ := by
        by_contra h
        exact hy (Coulomb.radialShellDensity_zero_inner (lt_of_not_ge h))
      rw [packetPotential_eq hb (by rw [norm_neg]; exact hbS.trans hyS), norm_neg]
      show ρ y * ‖y‖⁻¹ = ‖y‖⁻¹ * ρ y
      ring
  have hel : ∀ i, (∫ y, ρ y * packetPotential b (x i - y)) ≤ Coulomb.radialShellMoment S := by
    intro i
    refine le_trans (integral_mono_ae (hint _ (measurable_const.sub measurable_id))
      (Coulomb.radialShell_coulomb_integrable S (x i)) ?_) (shell_potential_le hS (x i))
    filter_upwards [Measure.ae_ne volume (x i)] with y hy
    have hw : x i - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (packetPotential_le hb hw) (hρ0 y)
  have hsum : (∑ i, ∫ y, ρ y * packetPotential b (x i - y)) ≤ N * Coulomb.radialShellMoment S := by
    calc _ ≤ ∑ _i : Fin N, Coulomb.radialShellMoment S := Finset.sum_le_sum fun i _ => hel i
      _ = N * Coulomb.radialShellMoment S := by simp
  rw [hnuc]
  push_cast
  linarith

/-- The shell average of the near count. -/
theorem shell_average_near {S r : ℝ} (hr : 0 < r) (hrS : 2 * r < S / 2) {N : ℕ}
    (x : Configuration N) :
    (∫ y, Coulomb.radialShellDensity S y * nearCount y r x) ≤
      4 * Real.pi / 3 * (2 * r) ^ 3 *
        ∑ i, {z : Position | 1 / 2 * S < ‖z‖ ∧ ‖z‖ < 3 * S}.indicator (fun _ => (1 : ℝ)) (x i) := by
  set ρ := Coulomb.radialShellDensity S with hρdef
  have hρi : Integrable ρ := Coulomb.radialShellDensity_integrable S
  have hρm : Measurable ρ := Coulomb.radialShellDensity_measurable S
  have hρ0 : ∀ y, 0 ≤ ρ y := Coulomb.radialShellDensity_nonneg S
  have hρ1 : ∀ y, ρ y ≤ 1 := Coulomb.radialShellDensity_le S
  have hS : 0 < S := by linarith
  have hind : ∀ i y, (Metric.closedBall y (2 * r)).indicator (fun _ => (1 : ℝ)) (x i) =
      (Metric.closedBall (x i) (2 * r)).indicator (fun _ => (1 : ℝ)) y := by
    intro i y
    by_cases h : x i ∈ Metric.closedBall y (2 * r)
    · have h' : y ∈ Metric.closedBall (x i) (2 * r) := by
        rw [Metric.mem_closedBall, dist_comm]; exact h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : y ∉ Metric.closedBall (x i) (2 * r) := by
        rw [Metric.mem_closedBall, dist_comm]; exact h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  have hint : ∀ i, Integrable (fun y => ρ y *
      (Metric.closedBall (x i) (2 * r)).indicator (fun _ => (1 : ℝ)) y) := by
    intro i
    refine hρi.mono' (hρm.mul (measurable_const.indicator measurableSet_closedBall)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 y)]
    have : |(Metric.closedBall (x i) (2 * r)).indicator (fun _ => (1 : ℝ)) y| ≤ 1 := by
      by_cases h : y ∈ Metric.closedBall (x i) (2 * r)
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]; norm_num
    nlinarith [hρ0 y, abs_nonneg ((Metric.closedBall (x i) (2 * r)).indicator (fun _ => (1 : ℝ)) y)]
  have he : (fun y => ρ y * nearCount y r x) = fun y => ∑ i, ρ y *
      (Metric.closedBall (x i) (2 * r)).indicator (fun _ => (1 : ℝ)) y := by
    funext y
    unfold nearCount
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hind]
  rw [he, integral_finsetSum _ fun i _ => hint i, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hA : x i ∈ {z : Position | 1 / 2 * S < ‖z‖ ∧ ‖z‖ < 3 * S}
  · rw [Set.indicator_of_mem hA, mul_one]
    calc (∫ y, ρ y * (Metric.closedBall (x i) (2 * r)).indicator (fun _ => (1 : ℝ)) y)
        ≤ ∫ y, (Metric.closedBall (x i) (2 * r)).indicator (fun _ => (1 : ℝ)) y := by
          apply integral_mono (hint i) ((integrable_indicator_iff measurableSet_closedBall).2
            (integrableOn_const (measure_closedBall_lt_top).ne))
          intro y
          have h0 : 0 ≤ (Metric.closedBall (x i) (2 * r)).indicator (fun _ => (1 : ℝ)) y :=
            Set.indicator_nonneg (fun _ _ => zero_le_one) y
          nlinarith [hρ1 y, hρ0 y]
      _ = 4 * Real.pi / 3 * (2 * r) ^ 3 := by
          rw [integral_indicator measurableSet_closedBall, integral_const, smul_eq_mul, mul_one,
            measureReal_restrict_apply_univ]
          exact Coulomb.volume_closedBall_three (x i) (by linarith)
  · rw [Set.indicator_of_notMem hA, mul_zero]
    apply le_of_eq
    rw [← integral_zero Position ℝ]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : ρ y = 0
    · simp [hy]
    · by_cases hb : y ∈ Metric.closedBall (x i) (2 * r)
      · exfalso
        apply hA
        have hy1 : S ≤ ‖y‖ := by
          by_contra h
          exact hy (Coulomb.radialShellDensity_zero_inner (lt_of_not_ge h))
        have hy2 : ‖y‖ < 2 * S := by
          by_contra h
          apply hy
          simp only [hρdef, Coulomb.radialShellDensity]
          apply Set.indicator_of_notMem
          intro hm
          have := hm.1
          simp only [Metric.mem_ball, dist_zero_right] at this
          exact h this
        rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] at hb
        have t1 := norm_sub_norm_le (x i) y
        have t2 := norm_sub_norm_le y (x i)
        rw [norm_sub_rev y (x i)] at t2
        constructor <;> linarith
      · simp [Set.indicator_of_notMem hb]

end

end AtomicIonization.IonizationGap
