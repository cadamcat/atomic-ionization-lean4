import AtomicIonization.AtomicBinding.Cutoff
import AtomicIonization.AtomicBinding.Insertion

namespace AtomicIonization.AtomicBinding

open OAI.NeutralAtom Filter
open scoped Topology
noncomputable section

theorem charge_coefficient_neg (Z n : ℕ) (hnZ : n + 1 ≤ Z) :
    (n : ℝ) / (8 * (Z : ℝ) - 4) - (Z : ℝ) / (8 * (Z : ℝ) + 2) < 0 := by
  have hZ : (1 : ℝ) ≤ Z := by exact_mod_cast (show 1 ≤ Z by omega)
  have hnZ' : (n : ℝ) + 1 ≤ Z := by exact_mod_cast hnZ
  apply sub_neg.mpr
  apply (div_lt_div_iff₀ (by linarith : 0 < 8 * (Z : ℝ) - 4)
    (by positivity : 0 < 8 * (Z : ℝ) + 2)).mpr
  nlinarith

theorem strict_trial_of_ground_state (Z : ℕ) {n : ℕ} (hnZ : n + 1 ≤ Z)
    {ψ : Wavefunction n} {g : Gradient n} (hd : OAI.NeutralAtom.FormDomain ψ g)
    (hm : OAI.NeutralAtom.normSquared ψ = 1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n),
      OAI.NeutralAtom.FormDomain χ h → OAI.NeutralAtom.normSquared χ = 1 →
      OAI.NeutralAtom.energy Z ψ g ≤ OAI.NeutralAtom.energy Z χ h) :
    ∃ (χ : Wavefunction (n+1)) (h : Gradient (n+1)),
      OAI.NeutralAtom.FormDomain χ h ∧ OAI.NeutralAtom.normSquared χ = 1 ∧
      OAI.NeutralAtom.energy Z χ h < OAI.NeutralAtom.energy Z ψ g := by
  have hZ : 1 ≤ Z := by omega
  let a : ℝ := (n : ℝ) / (8 * (Z : ℝ) - 4) - (Z : ℝ) / (8 * (Z : ℝ) + 2)
  let C : ℝ := distantMass⁻¹ * oneParticleGradientNorm bindingBump
  have ha : a < 0 := charge_coefficient_neg Z n hnZ
  obtain ⟨B, hB, hcompact⟩ := compact_ground_state_trials Z hd hm hmin
  have hlim : Tendsto (fun k => (B + (1 / 2 : ℝ) * C) * bindingScale k + a)
      atTop (𝓝 a) := by
    simpa using (bindingScale_tendsto.const_mul (B + (1 / 2 : ℝ) * C)).add_const a
  obtain ⟨k, hkcompact, hkerror⟩ :=
    (hcompact.and (hlim.eventually (Iio_mem_nhds ha))).exists
  obtain ⟨φ, p, hφ, hmφ, heφ, hsφ, hsp⟩ := hkcompact
  obtain ⟨χ, h, hχ, hmχ, heχ⟩ := compact_insertion_trial Z hZ hφ hmφ
    (show 0 < (k : ℝ) + 1 by positivity) hsφ hsp
  have herr : B * (bindingScale k)^2 + (1 / 2 : ℝ) * (bindingScale k)^2 * C +
      a * bindingScale k < 0 := by
    have H := mul_pos (bindingScale_pos k) (neg_pos.mpr hkerror)
    nlinarith only [H]
  refine ⟨χ, h, hχ, hmχ, ?_⟩
  change OAI.NeutralAtom.energy Z χ h ≤ OAI.NeutralAtom.energy Z φ p +
    (1 / 2 : ℝ) * ((bindingScale k)^2 * C) + a * bindingScale k at heχ
  linarith

end
end AtomicIonization.AtomicBinding

namespace AtomicIonization.Blueprint.Packages

theorem binding_proof (Z n : ℕ) (hn : 1 ≤ n) (hnZ : n ≤ Z) :
    groundEnergy Z n < groundEnergy Z (n - 1) := by
  revert hn hnZ
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
    intro hn hnZ
    have hZ : 1 ≤ Z := hn.trans hnZ
    cases n with
    | zero => simpa using AtomicBinding.binding_one Z hZ
    | succ m =>
      have hbprev := ih (by omega : 1 ≤ m + 1) (by omega : m + 1 ≤ Z)
      obtain ⟨ψ, g, hd, hm, he⟩ := AtomicBinding.attained_of_binding Z (m+1)
        (by omega) (by omega) hbprev
      have hmin : ∀ (χ : Wavefunction (m+1)) (h : Gradient (m+1)),
          OAI.NeutralAtom.FormDomain χ h → OAI.NeutralAtom.normSquared χ = 1 →
          OAI.NeutralAtom.energy Z ψ g ≤ OAI.NeutralAtom.energy Z χ h := by
        intro χ h hχ hmχ
        exact he.le.trans (AtomicBinding.energy_ge_groundEnergy Z (m+1) hZ hχ hmχ)
      obtain ⟨χ, h, hχ, hmχ, hlt⟩ := AtomicBinding.strict_trial_of_ground_state Z hnZ hd hm hmin
      have H := lt_of_le_of_lt (AtomicBinding.energy_ge_groundEnergy Z (m+1+1) hZ hχ hmχ) hlt
      change groundEnergy Z (m+1+1) < groundEnergy Z (m+1+1-1)
      simpa only [Nat.add_sub_cancel] using H.trans_eq he



end AtomicIonization.Blueprint.Packages
