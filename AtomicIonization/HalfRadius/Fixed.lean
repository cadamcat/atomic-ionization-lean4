import AtomicIonization.ModelBridge.GroundEnergyEqFormBottom
import AtomicIonization.AtomicBinding.Binding
import AtomicIonization.HalfRadius.Large
import AtomicIonization.Blueprint.Bridge
import OAI.Analysis.CoulombRadii.SpectralTheory.StrictBinding
import OAI.Analysis.CoulombRadii.FieldAnalysis.CorePointMeasurable

noncomputable section

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace AtomicIonization.HalfRadius

open OAI.Coulomb

theorem exteriorMass_le_binding_loss {n : ℕ} (u : H1Vector n) {r : ℝ} (hr : 0 < r) :
    OAI.Coulomb.exteriorMass u (2 * r) ≤
      (n : ℝ) * (mass u - mass (bindingLocalized u hr (fun _ => 1))) := by
  let v := bindingLocalized u hr (fun _ => 1)
  have hd (s : OAI.Coulomb.Spins n) :
      Integrable (fun x => ‖u.value s x‖ ^ 2 - ‖v.value s x‖ ^ 2) :=
    ((u.value_L2 s).integrable_norm_pow (by norm_num)).sub
      ((v.value_L2 s).integrable_norm_pow (by norm_num))
  have he : (n : ℝ) * (mass u - mass v) =
      ∑ s, ∫ x, (n : ℝ) * (‖u.value s x‖ ^ 2 - ‖v.value s x‖ ^ 2) := by
    simp only [mass, integral_const_mul,
      integral_sub ((u.value_L2 _).integrable_norm_pow (by norm_num))
        ((v.value_L2 _).integrable_norm_pow (by norm_num)),
      ← Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [he]
  unfold OAI.Coulomb.exteriorMass
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall fun x => mul_nonneg
      (Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num) (sq_nonneg _)
  · exact (hd s).const_mul n
  · filter_upwards [] with x
    by_cases hx : x ∈ configurationBox n r
    · have hcount : (∑ i : Fin n, if 2 * r < ‖position x i‖ then (1 : ℝ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact ite_eq_right (not_lt.mpr (hx i))
      rw [hcount, zero_mul]
      exact mul_nonneg (Nat.cast_nonneg n)
        (sub_nonneg.mpr (bindingLocalized_norm_le u hr s x))
    · have hv : v.value s x = 0 := bindingLocalized_value_outside u hr s x hx
      rw [hv, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      calc
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
        _ = (n : ℝ) := by simp

theorem uniform_exterior_upper_of_gap (Z : ℕ) (hZ : 1 ≤ Z) {n : ℕ} (hn : 0 < n)
    (E P : ℝ) (hE : (E : EReal) ≤ sectorFormBottom (atom Z hZ) n)
    (hP : (P : EReal) ≤ sectorFormBottom (atom Z hZ) (n - 1)) (hgap : E < P) :
    ∃ R : ℝ, 0 < R ∧ ∀ u : H1Vector n, Antisymmetric u → mass u = 1 →
      form (atom Z hZ) u = E → OAI.Coulomb.exteriorMass u R ≤ 1 / 2 := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let cap : ℝ := 1 / (2 * (n : ℝ))
  have hcap : 0 < cap := by dsimp [cap]; positivity
  have hg : 0 < P - E := sub_pos.mpr hgap
  obtain ⟨j, hj⟩ := ((binding_cost_tendsto n Z).eventually
    (gt_mem_nhds (mul_pos hg hcap))).exists
  let r : ℝ := (j : ℝ) + 1
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨2 * r, by positivity, ?_⟩
  intro u ha hm hf
  have hloss := binding_loss_bound Z hZ hn u ha hr E P hE hP
  rw [hm, hf, mul_one, sub_self, zero_add, mul_one] at hloss
  have hsmall : 3 * (n : ℝ) * (radialCutCoefficient / r) ^ 2 +
      (n : ℝ) * ((Z : ℝ) / r) ≤ (P - E) * cap := hj.le
  have hmass : mass u - mass (bindingLocalized u hr (fun _ => 1)) ≤ cap := by
    rw [hm]
    exact (mul_le_mul_iff_right₀ hg).mp (hloss.trans hsmall)
  calc
    OAI.Coulomb.exteriorMass u (2 * r) ≤
        (n : ℝ) * (mass u - mass (bindingLocalized u hr (fun _ => 1))) :=
      exteriorMass_le_binding_loss u hr
    _ ≤ (n : ℝ) * cap := mul_le_mul_of_nonneg_left hmass hn'.le
    _ = 1 / 2 := by dsimp [cap]; field_simp

theorem population_ball_le_nuclear (Z : ℕ) (hZ : 1 ≤ Z) {n : ℕ} (u : H1Vector n)
    {r : ℝ} (hr : 0 ≤ r) :
    expectedPopulation u (Metric.ball 0 r) ≤ r * nuclearEnergy (atom Z hZ) u := by
  have hZ' : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hpoint (x : OAI.Coulomb.Configuration n) (i : Fin n) (hx : position x i ≠ 0) :
      (Metric.ball (0 : Space) r).indicator (fun _ => (1 : ℝ)) (position x i) ≤
        (r * (Z : ℝ)) * ‖position x i‖⁻¹ := by
    by_cases hb : position x i ∈ Metric.ball (0 : Space) r
    · rw [indicator_of_mem hb]
      have hp : 0 < ‖position x i‖ := norm_pos_iff.mpr hx
      have hb' : ‖position x i‖ ≤ r := by simpa using (Metric.mem_ball.mp hb).le
      calc
        (1 : ℝ) ≤ r / ‖position x i‖ := (le_div_iff₀ hp).mpr (by simpa using hb')
        _ ≤ (r / ‖position x i‖) * (Z : ℝ) :=
          le_mul_of_one_le_right (div_nonneg hr (norm_nonneg _)) hZ'
        _ = _ := by ring
    · rw [indicator_of_notMem hb]
      positivity
  have H (s : OAI.Coulomb.Spins n) (i : Fin n) :
      (∫ x, (Metric.ball (0 : Space) r).indicator (fun _ => (1 : ℝ)) (position x i) *
        ‖u.value s x‖ ^ 2) ≤
      (r * (Z : ℝ)) * ∫ x, ‖position x i‖⁻¹ * ‖u.value s x‖ ^ 2 := by
    have hi : Integrable (fun x => ‖position x i‖⁻¹ * ‖u.value s x‖ ^ 2) := by
      simpa only [OAI.Coulomb.coulombKernel, sub_zero] using
        (u.nuclear_coulomb_integrable_bound s i 0 (by norm_num : (0 : ℝ) < 1)).1
    rw [← integral_const_mul]
    apply integral_mono_ae (population_integrable u _ measurableSet_ball s i)
      (hi.const_mul (r * (Z : ℝ)))
    filter_upwards [ae_position_ne n 0] with x hx
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hpoint x i (hx i)) (sq_nonneg _)
  calc
    expectedPopulation u (Metric.ball 0 r) ≤
        ∑ s, ∑ i : Fin n, (r * (Z : ℝ)) * ∫ x, ‖position x i‖⁻¹ * ‖u.value s x‖ ^ 2 :=
      Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun i _ => H s i
    _ = r * nuclearEnergy (atom Z hZ) u := by
      rw [nuclearEnergy_eq_sum]
      simp [atom, OAI.Coulomb.coulombKernel, Finset.mul_sum, mul_assoc]

theorem uniform_small_ball_of_form (Z : ℕ) (hZ : 1 ≤ Z) (n : ℕ) (E : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : H1Vector n, mass u = 1 → form (atom Z hZ) u = E →
      expectedPopulation u (Metric.ball 0 c) ≤ 1 / 4 := by
  let K : ℝ := 2 * |E| + 8 * (n : ℝ) * (Z : ℝ) ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let L : ℝ := 8 * (Z : ℝ) * K + (n : ℝ) * (Z : ℝ) / 4
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let c : ℝ := 1 / (4 * (L + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcL : c * L ≤ 1 / 4 := by
    calc
      c * L = L / (4 * (L + 1)) := by dsimp [c]; ring
      _ ≤ 1 / 4 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  refine ⟨c, hc, ?_⟩
  intro u hm hf
  have hk := kinetic_bound_of_form_bound (atom Z hZ) u
  have htotal : totalCharge (atom Z hZ) = (Z : ℝ) := by simp [totalCharge, atom]
  rw [hf, hm, htotal, mul_one] at hk
  have hk' : kinetic u ≤ K := by dsimp [K]; linarith [le_abs_self E]
  have hnuclear := nuclearEnergy_bound (atom Z hZ) u (by norm_num : (0 : ℝ) < 1)
  rw [hm, htotal, mul_one] at hnuclear
  have hnuclear' : nuclearEnergy (atom Z hZ) u ≤ L := by
    dsimp [L]
    apply hnuclear.trans
    gcongr
    norm_num
  exact (population_ball_le_nuclear Z hZ u hc.le).trans
    ((mul_le_mul_of_nonneg_left hnuclear' hc.le).trans hcL)

theorem neutral_energy_eq_groundEnergy {N : ℕ} {ψ : Wavefunction (N + 1)}
    {g : Gradient (N + 1)} (hd : FormDomain ψ g) (hn : normSquared ψ = 1)
    (hmin : ∀ (χ : Wavefunction (N + 1)) (h : Gradient (N + 1)),
      FormDomain χ h → normSquared χ = 1 → energy (N + 1) ψ g ≤ energy (N + 1) χ h) :
    energy (N + 1) ψ g = groundEnergy (N + 1) (N + 1) := by
  have hZ : 1 ≤ N + 1 := by omega
  have he : (energy (N + 1) ψ g : EReal) = sectorFormBottom (atom (N + 1) hZ) (N + 1) := by
    rw [← OAI.NeutralAtom.sectorEnergy_eq_formBottom (N + 1) hZ]
    apply le_antisymm
    · apply le_sInf
      rintro e ⟨χ, h, hχ, hm, rfl⟩
      exact EReal.coe_le_coe_iff.mpr (hmin χ h hχ hm)
    · exact OAI.NeutralAtom.sectorEnergy_le_trial hd hn
  exact EReal.coe_eq_coe_iff.mp (he.trans
    (Blueprint.Packages.groundEnergy_eq_formBottom_proof (N + 1) hZ (N + 1)).symm)

end AtomicIonization.HalfRadius

namespace AtomicIonization.Blueprint.Packages

theorem radius_bounds_fixed_proof (N : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ ∀ ψ : Wavefunction (N + 1), IsNormalizedGroundState (N + 1) ψ →
      c ≤ halfRadius ψ ∧ halfRadius ψ ≤ C := by
  have hZ : 1 ≤ N + 1 := by omega
  let E := groundEnergy (N + 1) (N + 1)
  let P := groundEnergy (N + 1) ((N + 1) - 1)
  have hE : (E : EReal) ≤
      OAI.Coulomb.sectorFormBottom (OAI.Coulomb.atom (N + 1) hZ) (N + 1) :=
    (groundEnergy_eq_formBottom_proof (N + 1) hZ (N + 1)).le
  have hP : (P : EReal) ≤
      OAI.Coulomb.sectorFormBottom (OAI.Coulomb.atom (N + 1) hZ) ((N + 1) - 1) :=
    (groundEnergy_eq_formBottom_proof (N + 1) hZ ((N + 1) - 1)).le
  have hgap : E < P := binding_proof (N + 1) (N + 1) hZ le_rfl
  obtain ⟨c, hc, HL⟩ := HalfRadius.uniform_small_ball_of_form (N + 1) hZ (N + 1) E
  obtain ⟨C, hC, HU⟩ := HalfRadius.uniform_exterior_upper_of_gap (N + 1) hZ
    (n := N + 1) (by omega) E P hE hP hgap
  refine ⟨c, C, hc, ?_⟩
  intro ψ hψ
  obtain ⟨g, hd, hn, hmin⟩ := hψ
  let u := OAI.NeutralAtom.asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1
  have hm : OAI.Coulomb.mass u = 1 := (OAI.NeutralAtom.asH1_mass ..).trans hn
  have hf : OAI.Coulomb.form (OAI.Coulomb.atom (N + 1) hZ) u = E :=
    (OAI.NeutralAtom.asH1_energy (N + 1) hZ hd.2.1 hd.2.2.1 hd.2.2.2.1).trans
      (HalfRadius.neutral_energy_eq_groundEnergy hd hn hmin)
  constructor
  · apply HalfRadius.halfRadius_ge_of_exteriorMass hd.2.2.1
    change (1 / 2 : ℝ) < OAI.NeutralAtom.exteriorMass ψ c
    rw [OAI.NeutralAtom.physical_exterior_deficit hd hn]
    have hcore := HL u hm hf
    linarith [Nat.cast_nonneg (α := ℝ) N]
  · apply csInf_le (s := {r : ℝ | 0 ≤ r ∧ exteriorMass ψ r ≤ (1 / 2 : ℝ)})
      ⟨0, fun r hr => hr.1⟩
    refine ⟨hC.le, ?_⟩
    change OAI.NeutralAtom.exteriorMass ψ C ≤ (1 / 2 : ℝ)
    rw [← OAI.NeutralAtom.asH1_exteriorMass hd C]
    exact HU u (OAI.NeutralAtom.asH1_antisymmetric hd) hm hf



end AtomicIonization.Blueprint.Packages
