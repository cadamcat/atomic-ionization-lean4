import OAI.Analysis.CoulombRadii.Localization.DeletionEnvelope

/-!
# Conditional inner fields on a shell at arbitrary energy offset

For a normalized antisymmetric state of energy at most `E + δ` above the unrestricted bottom `E`,
and an annular recorded ensemble at scale `r`, the positive part of the conditional field of the
nucleus and the inner particles `|x| < r/8`, evaluated on the shell `r ≤ |y| ≤ 2r`, has an envelope
whose data root mean square is at most `C (max(r⁻³, 1) + √(δ r)) / r`, uniformly in `δ ≥ 0`.
-/

namespace AtomicIonization.ExteriorTail

open OAI Coulomb

set_option maxHeartbeats 1000000 in
theorem biased_shell_envelope : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i = 0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ = 1 →
    ∀ {E δ : ℝ}, (E : EReal) ≤ unrestrictedFormBottom S → form S ψ ≤ E + δ → 0 ≤ δ →
    ∀ {r : ℝ}, 0 < r → ∀ T : RecordedEnsemble n,
      T.Conserves ψ → T.CoreFermionic →
      T.OutSupported {x : Space | r / 2 < ‖x‖ ∧ ‖x‖ < 4 * r} →
      T.totalMass = mass ψ → T.totalForm S ≤ form S ψ + annularIMSCost ψ r →
      ∃ M : T.InnerEnvelope S (r / 8) r, T.dataRMS M.value ≤ C * screenMass δ r / r := by
  obtain ⟨Cims, hCims, Hims⟩ := exists_atomic_annular_IMS_bound
  obtain ⟨Cf, hCf, Hfield⟩ := annular_ensemble_positive_field Cims hCims
  obtain ⟨Cm, hCm, Hmoment⟩ := atomic_annular_second_moment
    (α := (1 / 16 : ℝ)) (β := 9) (by norm_num) (by norm_num)
  obtain ⟨Cr, hCr, Hradial⟩ := atomic_radial_tail_second_moment
  obtain ⟨Cenv, hCenv, Henvelope⟩ := RecordedEnsemble.exists_inner_shell_envelope
  let B : ℝ := 2 * (Cf + 5000 * Real.sqrt Cm + 128 * Cr)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨Cenv * B, mul_nonneg hCenv hB, ?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ r hr T hlaw hf hsupp hmass hform
  let A : ℝ := screenMass δ r / r
  have hA : 0 ≤ A := div_nonneg (screenMass_pos δ r).le hr.le
  have hcost : annularIMSCost ψ r ≤ Cims * screenMass δ r / r ^ 2 :=
    Hims S hatom ψ hψ hm hE hstate hδ hr
  have htotalForm : T.totalForm S ≤ form S ψ + Cims * screenMass δ r / r ^ 2 :=
    hform.trans (add_le_add le_rfl hcost)
  have hfield := Hfield S hatom ψ hψ hm hE hstate hδ hr T hlaw hf hsupp hmass htotalForm
  have houterMeas : MeasurableSet
      {v : Space | (1 / 16 : ℝ) * r < ‖v‖ ∧ ‖v‖ < 9 * r} :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hcountSubset : {v : Space | r / 8 ≤ ‖v‖ ∧ ‖v‖ < 8 * r} ⊆
      {v : Space | (1 / 16 : ℝ) * r < ‖v‖ ∧ ‖v‖ < 9 * r} := by
    intro v hv
    constructor <;> nlinarith [hr, hv.1, hv.2]
  have hmoment := Hmoment S hatom ψ hψ hm hE hstate hδ hr
  have hcount : localCountSecondMoment ψ {v : Space | r / 8 ≤ ‖v‖ ∧ ‖v‖ < 8 * r} ≤
      Cm * (screenMass δ r) ^ 2 := by
    exact (localCountSecondMoment_mono ψ houterMeas hcountSubset).trans hmoment
  have hcountSqrt :
      Real.sqrt (localCountSecondMoment ψ {v : Space | r / 8 ≤ ‖v‖ ∧ ‖v‖ < 8 * r}) ≤
        Real.sqrt Cm * screenMass δ r := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) (screenMass_pos _ _).le, ?_⟩
    · rw [mul_pow, Real.sq_sqrt hCm]
      exact hcount
  have hscaleMass : screenMass δ (8 * r) ≤ 512 * screenMass δ r := by
    have hcmp : screenMass δ (8 * r) ≤ (8 : ℝ) ^ 3 * screenMass δ r :=
      screenMass_comparable (δ := δ) (a := r) (b := 8 * r) (q := 8) hδ hr
        (by norm_num : (1 : ℝ) ≤ 8)
        (by
          apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).2
          nlinarith [hr])
        (le_of_eq (mul_comm (8 : ℝ) r))
    norm_num at hcmp ⊢
    exact hcmp
  have htailRaw := Hradial S hatom ψ hψ hm hE hstate hδ (show 0 < 8 * r by positivity)
  have htail : rawRMS ψ (arrayStatistic (radialTailKernel (8 * r))) ≤ 64 * Cr * A := by
    calc
      _ ≤ Cr * screenMass δ (8 * r) / (8 * r) := htailRaw
      _ ≤ Cr * (512 * screenMass δ r) / (8 * r) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hscaleMass hCr) (by positivity)
      _ = 64 * Cr * A := by dsimp [A]; field_simp; ring
  have haddback := rawRMS_annularAddback ψ hr (r / 8)
  have hadd : rawRMS ψ (arrayStatistic (annularAddbackKernel (r / 8) r)) ≤
      (5000 * Real.sqrt Cm + 128 * Cr) * A := by
    calc
      _ ≤ (5000 / r) * (Real.sqrt Cm * screenMass δ r) +
            2 * (64 * Cr * A) := by
        exact haddback.trans (add_le_add
          (mul_le_mul_of_nonneg_left hcountSqrt (by positivity))
          (mul_le_mul_of_nonneg_left htail (by norm_num)))
      _ = (5000 * Real.sqrt Cm + 128 * Cr) * A := by dsimp [A]; ring
  have hpoint : ∀ y : Space, r / 2 ≤ ‖y‖ → ‖y‖ ≤ 4 * r →
      Real.sqrt (T.innerSquare S (r / 8) y) ≤ B * A := by
    intro y hylo hyhi
    have hraw : Real.sqrt (T.rawSquare S y (atomicCellScale y)) ≤ Cf * A := by
      simpa [A, mul_div_assoc] using hfield y hylo hyhi
    have hinner := hlaw.innerSquare_addback (u := r) (h := r / 8) S hr
      (by linarith [hr]) hylo hyhi
    calc
      _ ≤ 2 * (Real.sqrt (T.rawSquare S y (atomicCellScale y)) +
          rawRMS ψ (arrayStatistic (annularAddbackKernel (r / 8) r))) := hinner
      _ ≤ 2 * (Cf * A + (5000 * Real.sqrt Cm + 128 * Cr) * A) :=
        mul_le_mul_of_nonneg_left (add_le_add hraw hadd) (by norm_num)
      _ = B * A := by dsimp [B]; ring
  have hK : 0 ≤ B * A := mul_nonneg hB hA
  obtain ⟨M, hM⟩ := Henvelope S hatom T hr (by linarith [hr]) hK hpoint
  refine ⟨M, ?_⟩
  calc
    T.dataRMS M.value ≤ Cenv * (B * A) := hM
    _ = Cenv * B * screenMass δ r / r := by dsimp [A]; ring

end AtomicIonization.ExteriorTail
