import AtomicIonization.Blueprint.Bridge
import OAI.Analysis.CoulombRadii.LimitTheory.NeutralCountControl

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace AtomicIonization.HalfRadius

theorem halfRadius_set_nonempty {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) :
    {r : ℝ | 0 ≤ r ∧ exteriorMass ψ r ≤ (1 / 2 : ℝ)}.Nonempty := by
  have he := (OAI.NeutralAtom.exteriorMass_tendsto_zero hψ).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨r, hr, hmass⟩ := ((eventually_ge_atTop (0 : ℝ)).and he).exists
  exact ⟨r, hr, hmass.le⟩

theorem halfRadius_ge_of_exteriorMass {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) {r : ℝ}
    (hmass : (1 / 2 : ℝ) < exteriorMass ψ r) : r ≤ halfRadius ψ := by
  apply le_csInf (halfRadius_set_nonempty hψ)
  intro s hs
  by_contra! hsr
  have hmono := OAI.NeutralAtom.exteriorMass_antitone hψ hsr.le
  exact (not_le_of_gt hmass) (hmono.trans hs.2)

theorem neutral_exterior_lower_large :
    ∃ c : ℝ, 0 < c ∧ ∃ Z₀ : ℕ, ∀ N : ℕ, Z₀ ≤ N + 1 →
      ∀ ψ : Wavefunction (N + 1), IsNormalizedGroundState (N + 1) ψ →
        1 ≤ exteriorMass ψ c := by
  obtain ⟨D, hD, Zd, HD⟩ := OAI.NeutralAtom.physical_neutral_energy_offset
  obtain ⟨a, M, ha, hM, H⟩ := OAI.NeutralAtom.physical_propagated_core_mean
  obtain ⟨s₀, hs₀, H⟩ := H D hD
  have ht : Tendsto (fun s : ℝ => s ^ 3 + M * s ^ 12) (𝓝[>] 0) (𝓝 0) := by
    convert ((tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0)).pow 3).add
      (((tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0)).pow 12).const_mul M) using 1 <;> simp
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s ∧ s < s₀ ∧ s ^ 3 + M * s ^ 12 < a :=
    (show ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s from self_mem_nhdsWithin).and
      (((gt_mem_nhds hs₀).filter_mono nhdsWithin_le_nhds).and
        (ht.eventually (gt_mem_nhds ha)))
  obtain ⟨s, hs, hss, hsa⟩ := hsmall.exists
  obtain ⟨Zp, HP⟩ := H s hs hss
  refine ⟨s / 4, by positivity, max Zd Zp, ?_⟩
  intro N hN ψ hψ
  obtain ⟨g, hd, hn, hmin⟩ := hψ
  have hZ : 1 ≤ N + 1 := by omega
  let u := OAI.NeutralAtom.asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1
  have hm : OAI.Coulomb.mass u = 1 := (OAI.NeutralAtom.asH1_mass ..).trans hn
  have hE := OAI.Coulomb.atom_unrestricted_bottom_real (N + 1) hZ u
    (OAI.NeutralAtom.asH1_antisymmetric hd) hm
  have he := HD (N + 1) ((le_max_left _ _).trans hN) hZ hd hn hmin
  have hcore := HP (N + 1) ((le_max_right _ _).trans hN) hZ hd hn hmin
    hE.le he (by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) N])
  have hdeficit : 1 + M * s ^ 9 ≤ a / s ^ 3 := by
    apply (le_div_iff₀ (pow_pos hs 3)).mpr
    calc
      _ = s ^ 3 + M * s ^ 12 := by ring
      _ ≤ a := hsa.le
  change 1 ≤ OAI.NeutralAtom.exteriorMass ψ (s / 4)
  rw [OAI.NeutralAtom.physical_exterior_deficit hd hn]
  push_cast at hcore
  linarith only [hcore, hdeficit]

end AtomicIonization.HalfRadius

namespace AtomicIonization.Blueprint.Packages

theorem radius_lower_large_proof :
    ∃ c : ℝ, 0 < c ∧ ∃ Z₀ : ℕ, ∀ N : ℕ, Z₀ ≤ N + 1 →
      ∀ ψ : Wavefunction (N + 1), IsNormalizedGroundState (N + 1) ψ →
        c ≤ halfRadius ψ := by
  obtain ⟨c, hc, Z₀, H⟩ := HalfRadius.neutral_exterior_lower_large
  refine ⟨c, hc, Z₀, ?_⟩
  intro N hN ψ hψ
  have hext := H N hN ψ hψ
  obtain ⟨g, hd, hn, hmin⟩ := hψ
  exact HalfRadius.halfRadius_ge_of_exteriorMass hd.2.2.1 (by linarith)



end AtomicIonization.Blueprint.Packages
