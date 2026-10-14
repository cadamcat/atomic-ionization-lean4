import AtomicIonization.AtomicBinding.Packet

namespace AtomicIonization.AtomicBinding

open OAI.NeutralAtom MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section

theorem potential_insert_le_with_attraction {n : ℕ} (Z : ℕ)
    {ψ : Wavefunction n} {g : Gradient n} (h : FormRegular ψ g)
    {R d b : ℝ} (hd : 0 < d) (hRd : R < d)
    (hψ : ∀ σ x, R < ‖x‖ → ψ σ x = 0)
    {f : Position → ℝ} (hfLp : MemLp f 2 volume)
    (hfout : ∀ y, ‖y‖ ≤ d → f y = 0)
    (hfin : ∀ y, b ≤ ‖y‖ → f y = 0)
    (hi : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g)) :
    potentialForm Z (insertWavefunction f ψ) ≤
      (∫ y : Position, (f y)^2) * potentialForm Z ψ +
        ((n : ℝ) * (d - R)⁻¹ - (Z : ℝ) * b⁻¹) * normSquared (insertWavefunction f ψ) := by
  let C : ℝ := (n : ℝ) * (d - R)⁻¹ - (Z : ℝ) * b⁻¹
  have hold (σ : Spins (n+1)) : Integrable (fun x : Configuration (n+1) =>
      coulombPotential Z (fun i => x i.succ) * ‖insertWavefunction f ψ σ x‖^2) := by
    by_cases hσ : σ 0 = 0
    · simpa only [insertWavefunction, hσ, ↓reduceIte] using
        integrable_weighted_tensor hfLp (h.integrable_potential Z (fun i => σ i.succ))
    · simp [insertWavefunction, hσ]
  have hnew (σ : Spins (n+1)) := ((hi.2.1 σ).norm.integrable_sq).const_mul C
  have hb (σ : Spins (n+1)) (x : Configuration (n+1)) :
      coulombPotential Z x * ‖insertWavefunction f ψ σ x‖^2 ≤
        coulombPotential Z (fun i => x i.succ) * ‖insertWavefunction f ψ σ x‖^2 +
          C * ‖insertWavefunction f ψ σ x‖^2 := by
    by_cases hx : insertWavefunction f ψ σ x = 0
    · simp [hx]
    · have he : x = Fin.cons (x 0) (fun i => x i.succ) := by
        ext i; cases i using Fin.cases <;> rfl
      have hsum : (∑ i : Fin n, ‖x 0 - x i.succ‖⁻¹) ≤ (n : ℝ) * (d - R)⁻¹ := by
        calc
          _ ≤ ∑ _i : Fin n, (d - R)⁻¹ := Finset.sum_le_sum fun i _ =>
            (le_abs_self _).trans (inserted_pair_bound hRd hfout hψ σ x i hx)
          _ = _ := by simp
      have hlow : d < ‖x 0‖ := by
        by_contra hh
        exact hx (by simp [insertWavefunction, hfout (x 0) (le_of_not_gt hh)])
      have hupp : ‖x 0‖ < b := by
        by_contra hh
        exact hx (by simp [insertWavefunction, hfin (x 0) (le_of_not_gt hh)])
      have hat : b⁻¹ ≤ ‖x 0‖⁻¹ := inv_anti₀ (hd.trans hlow) hupp.le
      have hat' := mul_le_mul_of_nonneg_left hat (Nat.cast_nonneg (α := ℝ) Z)
      have hpot : coulombPotential Z x ≤ coulombPotential Z (fun i => x i.succ) + C := by
        conv_lhs => rw [he, coulombPotential_cons]
        dsimp [C]
        linarith
      simpa only [add_mul] using
        mul_le_mul_of_nonneg_right hpot (sq_nonneg ‖insertWavefunction f ψ σ x‖)
  have hiσ (σ : Spins (n+1)) :
      (∫ x, coulombPotential Z x * ‖insertWavefunction f ψ σ x‖^2) ≤
        (∫ x, coulombPotential Z (fun i => x i.succ) * ‖insertWavefunction f ψ σ x‖^2) +
          C * (∫ x, ‖insertWavefunction f ψ σ x‖^2) := by
    have H := integral_mono (hi.integrable_potential Z σ) ((hold σ).add (hnew σ)) (hb σ)
    change _ ≤ ∫ x, coulombPotential Z (fun i => x i.succ) * ‖insertWavefunction f ψ σ x‖^2 +
      C * ‖insertWavefunction f ψ σ x‖^2 at H
    rw [integral_add (hold σ) (hnew σ), integral_const_mul] at H
    exact H
  have H := Finset.sum_le_sum (s := Finset.univ) (fun σ _ => hiσ σ)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at H
  rw [weighted_normSquared_insert] at H
  exact H

theorem energy_insert_le_with_attraction {n : ℕ} (Z : ℕ)
    {ψ : Wavefunction n} {g : Gradient n} (h : FormRegular ψ g)
    (hn : OAI.NeutralAtom.normSquared ψ = 1) {R d b : ℝ} (hd : 0 < d) (hRd : R < d)
    (hψ : ∀ σ x, R < ‖x‖ → ψ σ x = 0)
    {f : Position → ℝ} (hfLp : MemLp f 2 volume) (hfn : (∫ y : Position, (f y)^2) = 1)
    (hfout : ∀ y, ‖y‖ ≤ d → f y = 0)
    (hfin : ∀ y, b ≤ ‖y‖ → f y = 0)
    (hi : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g)) :
    OAI.NeutralAtom.energy Z (insertWavefunction f ψ) (insertGradient f ψ g) ≤
      OAI.NeutralAtom.energy Z ψ g + (1 / 2 : ℝ) * oneParticleGradientNorm f +
        ((n : ℝ) * (d - R)⁻¹ - (Z : ℝ) * b⁻¹) := by
  have hp := potential_insert_le_with_attraction Z h hd hRd hψ hfLp hfout hfin hi
  simp only [hfn, normSquared_insert, hn, one_mul, mul_one] at hp
  rw [energy_decompose, energy_decompose, gradientNormSquared_insert, hfn, hn, one_mul, mul_one]
  linarith

theorem compact_insertion_trial (Z : ℕ) (hZ : 1 ≤ Z) {n : ℕ}
    {ψ : Wavefunction n} {g : Gradient n} (hd : OAI.NeutralAtom.FormDomain ψ g)
    (hn : OAI.NeutralAtom.normSquared ψ = 1) {t : ℝ} (ht : 0 < t)
    (hψ : ∀ σ x, 2 * t < ‖x‖ → ψ σ x = 0)
    (hg : ∀ σ i a x, 2 * t < ‖x‖ → g σ i a x = 0) :
    ∃ (χ : Wavefunction (n+1)) (h : Gradient (n+1)),
      OAI.NeutralAtom.FormDomain χ h ∧ OAI.NeutralAtom.normSquared χ = 1 ∧
      OAI.NeutralAtom.energy Z χ h ≤ OAI.NeutralAtom.energy Z ψ g +
        (1 / 2 : ℝ) * (t⁻¹^2 * (distantMass⁻¹ * oneParticleGradientNorm bindingBump)) +
        ((n : ℝ) / (8 * (Z : ℝ) - 4) - (Z : ℝ) / (8 * (Z : ℝ) + 2)) * t⁻¹ := by
  have hZ' : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  let d : ℝ := (8 * (Z : ℝ) - 2) * t
  let b : ℝ := (8 * (Z : ℝ) + 2) * t
  let f := chargePacket Z t
  have hdpos : 0 < d := by dsimp [d]; exact mul_pos (by linarith) ht
  have hRd : 2 * t < d := by dsimp [d]; nlinarith
  have hfLp : MemLp f 2 volume := chargePacket_memLp Z ht
  have hfn : (∫ y : Position, (f y)^2) = 1 := chargePacket_normalized Z ht
  have hfout : ∀ y, ‖y‖ ≤ d → f y = 0 := fun _ hy => chargePacket_inner_zero Z ht hy
  have hfin : ∀ y, b ≤ ‖y‖ → f y = 0 := fun _ hy => chargePacket_outer_zero Z ht hy
  have hi : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g) :=
    FormRegular.insert_separated hd.2 hdpos hRd hψ (chargePacket_smooth Z t) hfLp
      (fun a => chargePacket_derivative_memLp Z ht _) hfout
  have hfs : ∀ y, ‖y‖ ≤ 2 * t → f y = 0 := fun y hy => hfout y (hy.trans hRd.le)
  have hs := insertionSupport_tensor hfs hψ
  have hgs : ∀ i a, InsertionSupport (2 * t) (fun σ x => insertGradient f ψ g σ i a x) :=
    insertionSupport_gradient hfs (fun _ _ hy => chargePacket_derivative_zero Z hZ ht hy _) hψ hg
  let c : ℝ := (Real.sqrt (n+1 : ℝ))⁻¹
  have hc : c^2 * (n+1 : ℝ) = 1 := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt (by positivity), inv_mul_cancel₀ (by positivity)]
  refine ⟨scaleWavefunction c (wedgeInsert f ψ), scaleGradient c (wedgeInsertGradient f ψ g),
    (hi.wedgeInsert hd.1).scale c, ?_, ?_⟩
  · rw [normSquared_scale, normSquared_wedgeInsert hd.2.2.1 hfLp hs,
      normSquared_insert, hfn, hn]
    simpa only [one_mul, mul_one] using hc
  · rw [energy_scale, energy_wedgeInsert Z hi hs hgs, ← mul_assoc, hc, one_mul]
    have H := energy_insert_le_with_attraction Z hd.2 hn hdpos hRd hψ hfLp hfn hfout hfin hi
    rw [chargePacket_gradientNorm Z ht] at H
    convert H using 1
    have hdR : d - 2 * t = (8 * (Z : ℝ) - 4) * t := by dsimp [d]; ring
    rw [hdR]
    dsimp [b]
    simp only [mul_inv_rev, div_eq_mul_inv]
    ring

end
end AtomicIonization.AtomicBinding
