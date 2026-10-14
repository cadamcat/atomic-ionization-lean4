import OAI.Analysis.CoulombRadii.FieldAnalysis.NewtonInterior

/-!
# The potential of a uniform spherical shell

The Coulomb potential of the uniform shell `{h ≤ |y| < 2h}` is largest at the center: at every
point it is at most its central value `radialShellMoment h`.
-/

namespace AtomicIonization.IonizationGap

open OAI MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The potential of a radial profile decreases with the distance from the center. -/
theorem radial_lintegral_antitone (F : ℝ → ℝ≥0∞) (hF : Measurable F) {x x' : Coulomb.Space}
    (hx' : x' ≠ 0) (hxx : ‖x'‖ ≤ ‖x‖) :
    (∫⁻ y : Coulomb.Space, ENNReal.ofReal ‖x - y‖⁻¹ * F ‖y‖) ≤
      ∫⁻ y : Coulomb.Space, ENNReal.ofReal ‖x' - y‖⁻¹ * F ‖y‖ := by
  have hx : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hxx
    exact hx' (norm_le_zero_iff.mp hxx)
  rw [Coulomb.radial_coulomb_lintegral F hF hx, Coulomb.radial_coulomb_lintegral F hF hx']
  gcongr with s

theorem shell_lintegral_eq (h : ℝ) (w : Coulomb.Space) :
    ENNReal.ofReal (∫ y, Coulomb.coulombKernel (w - y) * Coulomb.radialShellDensity h y) =
      ∫⁻ y : Coulomb.Space, ENNReal.ofReal ‖w - y‖⁻¹ *
        ENNReal.ofReal (Coulomb.radialShellDensity h (EuclideanSpace.single 0 ‖y‖)) := by
  rw [ofReal_integral_eq_lintegral_ofReal (Coulomb.radialShell_coulomb_integrable h w)
    (Filter.Eventually.of_forall fun y =>
      mul_nonneg (Coulomb.coulombKernel_nonneg _) (Coulomb.radialShellDensity_nonneg h y))]
  apply lintegral_congr
  intro y
  rw [ENNReal.ofReal_mul (Coulomb.coulombKernel_nonneg _), ← Coulomb.radialShellDensity_radial h y]
  rfl

/-- The potential of the uniform shell is at most its central value. -/
theorem shell_potential_le {h : ℝ} (hh : 0 < h) (w : Coulomb.Space) :
    (∫ y, Coulomb.coulombKernel (w - y) * Coulomb.radialShellDensity h y) ≤
      Coulomb.radialShellMoment h := by
  by_cases hw : ‖w‖ ≤ h
  · exact (Coulomb.radialShell_coulomb_inner hw).le
  · let x' : Coulomb.Space := EuclideanSpace.single 0 h
    have hx'n : ‖x'‖ = h := by simp [x', abs_of_pos hh]
    have hx' : x' ≠ 0 := by
      intro he
      rw [he, norm_zero] at hx'n
      linarith
    have hF : Measurable fun s : ℝ =>
        ENNReal.ofReal (Coulomb.radialShellDensity h (EuclideanSpace.single 0 s)) :=
      ((Coulomb.radialShellDensity_measurable h).comp
        Coulomb.space_axis_continuous.measurable).ennreal_ofReal
    have hle : ‖x'‖ ≤ ‖w‖ := by rw [hx'n]; exact (lt_of_not_ge hw).le
    have H := radial_lintegral_antitone _ hF hx' hle
    rw [← shell_lintegral_eq, ← shell_lintegral_eq,
      Coulomb.radialShell_coulomb_inner hx'n.le] at H
    exact (ENNReal.ofReal_le_ofReal_iff (Coulomb.radialShellMoment_pos hh).le).mp H

end

end AtomicIonization.IonizationGap
