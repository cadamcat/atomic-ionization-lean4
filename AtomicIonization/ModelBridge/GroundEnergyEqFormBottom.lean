import AtomicIonization.Blueprint.Bridge

namespace AtomicIonization.ModelBridge

open AtomicIonization

private def realTrialEnergies (Z n : ℕ) : Set ℝ :=
  {e | ∃ (ψ : Wavefunction n) (g : Gradient n),
    FormDomain ψ g ∧ normSquared ψ = 1 ∧ energy Z ψ g = e}

private def extendedTrialEnergies (Z n : ℕ) : Set EReal :=
  {e | ∃ (ψ : Wavefunction n) (g : Gradient n),
    FormDomain ψ g ∧ normSquared ψ = 1 ∧ e = (energy Z ψ g : EReal)}

private lemma real_sInf_coe_eq_sInf_coe_image {S : Set ℝ} (hne : S.Nonempty)
    (hbdd : BddBelow S) :
    ((sInf S : ℝ) : EReal) = sInf ((fun x : ℝ => (x : EReal)) '' S) := by
  have hglb : IsGLB ((fun x : ℝ => (x : EReal)) '' S) ((sInf S : ℝ) : EReal) := by
    constructor
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact EReal.coe_le_coe_iff.mpr (csInf_le hbdd hx)
    · intro y hy
      cases y using EReal.rec with
      | bot => exact bot_le
      | coe x =>
        apply EReal.coe_le_coe_iff.mpr
        apply le_csInf hne
        intro z hz
        exact EReal.coe_le_coe_iff.mp
          (hy (Set.mem_image_of_mem _ hz))
      | top =>
        rcases hne with ⟨x, hx⟩
        have htop : (⊤ : EReal) ≤ (x : EReal) :=
          hy (Set.mem_image_of_mem _ hx)
        simp at htop
  exact hglb.unique (isGLB_sInf _)

end AtomicIonization.ModelBridge

namespace AtomicIonization.Blueprint.Packages

open AtomicIonization

theorem groundEnergy_eq_formBottom_proof (Z : ℕ) (hZ : 1 ≤ Z) (n : ℕ) :
    ((groundEnergy Z n : ℝ) : EReal) =
      OAI.Coulomb.sectorFormBottom (OAI.Coulomb.atom Z hZ) n := by
  by_cases hn0 : n = 0
  · subst n
    rw [← OAI.NeutralAtom.sectorEnergy_eq_formBottom Z hZ 0,
      OAI.NeutralAtom.sectorEnergy_vacuum]
    simp [groundEnergy]
  · let bottom : EReal := OAI.Coulomb.sectorFormBottom (OAI.Coulomb.atom Z hZ) n
    have hbottom_real : (bottom.toReal : EReal) = bottom := by
      exact OAI.Coulomb.atom_sectorFormBottom_real Z hZ n
    have hsector : OAI.NeutralAtom.sectorEnergy Z n = (bottom.toReal : EReal) := by
      rw [OAI.NeutralAtom.sectorEnergy_eq_formBottom Z hZ n]
      exact hbottom_real.symm
    have hsector_def : OAI.NeutralAtom.sectorEnergy Z n =
        sInf (AtomicIonization.ModelBridge.extendedTrialEnergies Z n) := by
      rfl
    have hT_nonempty : (AtomicIonization.ModelBridge.extendedTrialEnergies Z n).Nonempty := by
      by_contra hT
      have hT_empty : AtomicIonization.ModelBridge.extendedTrialEnergies Z n = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hT
      have htop : OAI.NeutralAtom.sectorEnergy Z n = ⊤ := by
        rw [hsector_def, hT_empty]
        simp
      rw [hsector] at htop
      exact EReal.coe_ne_top _ htop
    have hS_nonempty : (AtomicIonization.ModelBridge.realTrialEnergies Z n).Nonempty := by
      rcases hT_nonempty with ⟨e, ψ, g, hd, hn, he⟩
      exact ⟨energy Z ψ g, ⟨ψ, g, hd, hn, rfl⟩⟩
    have hS_bdd : BddBelow (AtomicIonization.ModelBridge.realTrialEnergies Z n) := by
      refine ⟨bottom.toReal, ?_⟩
      intro e he
      rcases he with ⟨ψ, g, hd, hn, rfl⟩
      have hle := OAI.NeutralAtom.sectorEnergy_le_trial
        (Z := Z) (ψ := ψ) (g := g)
        (show OAI.NeutralAtom.FormDomain ψ g from hd)
        (show OAI.NeutralAtom.normSquared ψ = 1 from hn)
      have hle' : (bottom.toReal : EReal) ≤ (energy Z ψ g : EReal) := by
        calc
          (bottom.toReal : EReal) = OAI.NeutralAtom.sectorEnergy Z n := hsector.symm
          _ ≤ (energy Z ψ g : EReal) := hle
      exact EReal.coe_le_coe_iff.mp hle'
    have himage : AtomicIonization.ModelBridge.extendedTrialEnergies Z n =
        (fun e : ℝ => (e : EReal)) ''
          AtomicIonization.ModelBridge.realTrialEnergies Z n := by
      ext e
      constructor
      · rintro ⟨ψ, g, hd, hn, he⟩
        refine ⟨energy Z ψ g, ⟨ψ, g, hd, hn, rfl⟩, ?_⟩
        exact he.symm
      · rintro ⟨x, ⟨ψ, g, hd, hn, hx⟩, hxe⟩
        refine ⟨ψ, g, hd, hn, ?_⟩
        calc
          e = (x : EReal) := hxe.symm
          _ = (energy Z ψ g : EReal) := by rw [hx]
    calc
      ((groundEnergy Z n : ℝ) : EReal) =
          ((sInf (AtomicIonization.ModelBridge.realTrialEnergies Z n) : ℝ) : EReal) := by
        simp [groundEnergy, hn0, AtomicIonization.ModelBridge.realTrialEnergies]
      _ = OAI.NeutralAtom.sectorEnergy Z n := by
        rw [AtomicIonization.ModelBridge.real_sInf_coe_eq_sInf_coe_image
          hS_nonempty hS_bdd, ← himage]
        exact hsector_def.symm
      _ = OAI.Coulomb.sectorFormBottom (OAI.Coulomb.atom Z hZ) n :=
        OAI.NeutralAtom.sectorEnergy_eq_formBottom Z hZ n

