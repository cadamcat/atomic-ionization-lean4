import AtomicIonization.AtomicBinding.Attainment
import OAI.Analysis.CoulombRadii.FormDomain.ExplicitMultiplyGradient

namespace AtomicIonization.AtomicBinding

open OAI OAI.NeutralAtom MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section

theorem energy_ge_groundEnergy (Z n : ℕ) (hZ : 1 ≤ Z)
    {ψ : Wavefunction n} {g : Gradient n} (hd : AtomicIonization.FormDomain ψ g)
    (hm : AtomicIonization.normSquared ψ = 1) :
    groundEnergy Z n ≤ AtomicIonization.energy Z ψ g := by
  apply EReal.coe_le_coe_iff.mp
  rw [Blueprint.Packages.groundEnergy_eq_formBottom_proof Z hZ n,
    ← sectorEnergy_eq_formBottom Z hZ n]
  exact sectorEnergy_le_trial hd hm

theorem compact_ground_state_trials (Z : ℕ) {n : ℕ}
    {ψ : Wavefunction n} {g : Gradient n} (hd : OAI.NeutralAtom.FormDomain ψ g)
    (hm : OAI.NeutralAtom.normSquared ψ = 1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n),
      OAI.NeutralAtom.FormDomain χ h → OAI.NeutralAtom.normSquared χ = 1 →
      OAI.NeutralAtom.energy Z ψ g ≤ OAI.NeutralAtom.energy Z χ h) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop,
      ∃ (χ : Wavefunction n) (h : Gradient n),
        OAI.NeutralAtom.FormDomain χ h ∧ OAI.NeutralAtom.normSquared χ = 1 ∧
        OAI.NeutralAtom.energy Z χ h ≤ OAI.NeutralAtom.energy Z ψ g + B * (bindingScale k)^2 ∧
        (∀ σ x, 2 * ((k : ℝ) + 1) < ‖x‖ → χ σ x = 0) ∧
        (∀ σ i a x, 2 * ((k : ℝ) + 1) < ‖x‖ → h σ i a x = 0) := by
  obtain ⟨C, hC, hb⟩ := bindingCutoff_derivative_bounded n
  let D : Fin n → Fin 3 → ℝ := fun i a => C * ‖OAI.NeutralAtom.coordinateDirection i a‖
  let A : ℝ := (1 / 2 : ℝ) * ∑ i : Fin n, ∑ a : Fin 3, (D i a)^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨2 * A, by positivity, ?_⟩
  have hmass : Tendsto (fun k => OAI.NeutralAtom.normSquared
      (multiplyWavefunction (expandingCutoff n k) ψ)) atTop (𝓝 1) := by
    simpa only [hm] using normSquared_cutoff_tendsto hd
  filter_upwards [hmass.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))]
    with k hk
  let θ := expandingCutoff n k
  let χ := multiplyWavefunction θ ψ
  let h := multiplyGradient θ ψ g
  let c := (Real.sqrt (OAI.NeutralAtom.normSquared χ))⁻¹
  have hθ : SmoothMultiplier θ := expandingCutoff_multiplier n k
  have hnχ : 0 < OAI.NeutralAtom.normSquared χ := by dsimp [χ, θ]; linarith
  have hc : c^2 = (OAI.NeutralAtom.normSquared χ)⁻¹ := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt hnχ.le]
  have he : OAI.NeutralAtom.energy Z χ h =
      OAI.NeutralAtom.energy Z ψ g * OAI.NeutralAtom.normSquared χ + localizationError ψ θ := by
    have hsq : SmoothMultiplier (fun x => θ x^2) := by
      simpa only [pow_two] using hθ.mul hθ
    rw [energy_localization_identity Z hd hθ, minimizer_multiplier_pairing Z hd hm hmin hsq]
    simp only [stateWeightedIntegral, OAI.NeutralAtom.normSquared, χ, norm_multiplyWavefunction_sq]
  have herr : localizationError ψ θ ≤ A * (bindingScale k)^2 := by
    have H := localizationError_le hd.2.2.1 hθ
      (fun i a => bindingScale k * D i a) (fun i a x => by
        rw [expandingCutoff_fderiv, abs_mul, abs_of_pos (bindingScale_pos k)]
        apply mul_le_mul_of_nonneg_left _ (bindingScale_pos k).le
        exact ((fderiv ℝ (bindingCutoff n) (bindingScale k • x)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)))
    rw [hm, mul_one] at H
    convert H using 1
    dsimp [A]
    simp only [mul_pow, ← Finset.mul_sum]
    ring
  refine ⟨scaleWavefunction c χ, scaleGradient c h, (hd.multiply hθ).scale c, ?_, ?_, ?_, ?_⟩
  · rw [normSquared_scale, hc, inv_mul_cancel₀ hnχ.ne']
  · rw [energy_scale, hc, he]
    have hi : (OAI.NeutralAtom.normSquared χ)⁻¹ ≤ 2 := by
      have H := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hk.le
      norm_num at H
      exact H
    have hmul := mul_le_mul_of_nonneg_left herr (inv_nonneg.mpr hnχ.le)
    have hmul' := mul_le_mul_of_nonneg_right hi (mul_nonneg hA (sq_nonneg (bindingScale k)))
    rw [mul_add, mul_left_comm (OAI.NeutralAtom.normSquared χ)⁻¹
      (OAI.NeutralAtom.energy Z ψ g), inv_mul_cancel₀ hnχ.ne', mul_one]
    nlinarith only [hmul, hmul']
  · intro σ x hx
    simp [scaleWavefunction, χ, θ, multiplyWavefunction, expandingCutoff_eq_zero hx]
  · intro σ i a x hx
    simp [scaleGradient, h, θ, multiplyGradient, expandingCutoff_eq_zero hx,
      expandingCutoff_fderiv_eq_zero hx]

end
end AtomicIonization.AtomicBinding
