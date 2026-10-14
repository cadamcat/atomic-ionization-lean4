import AtomicIonization.Blueprint.Interfaces
import AtomicIonization.Blueprint.Finite

/-!
# Assembly of `AtomicIonization.Statement` from the package interfaces
-/

namespace AtomicIonization.Blueprint

open AtomicIonization

theorem first_ionization_bounds_of (hgap : type_of% @Packages.ionization_gap)
    (hupper : type_of% @Packages.ionization_upper) (hbind : type_of% @Packages.binding) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ Z : ℕ, 1 ≤ Z →
      c ≤ ionizationEnergy 1 Z ∧ ionizationEnergy 1 Z ≤ C := by
  obtain ⟨c, hc, Z₂, hgap⟩ := hgap
  obtain ⟨C, hC⟩ := hupper
  obtain ⟨c₁, hc₁, hsmall⟩ := finite_lower (fun Z c => 1 ≤ Z → c ≤ ionizationEnergy 1 Z)
    (fun _ c c' hcc' h hZ => hcc'.trans (h hZ)) Z₂ (fun Z _ => by
      by_cases hZ : 1 ≤ Z
      · refine ⟨ionizationEnergy 1 Z, ?_, fun _ => le_rfl⟩
        have := hbind Z Z hZ le_rfl
        simp only [ionizationEnergy]
        linarith
      · exact ⟨1, one_pos, fun h => absurd h hZ⟩)
  refine ⟨min c c₁, max C (min c c₁), lt_min hc hc₁, le_max_right _ _, fun Z hZ => ⟨?_, ?_⟩⟩
  · by_cases hZ₂ : Z₂ ≤ Z
    · exact (min_le_left _ _).trans (hgap Z hZ₂ hZ)
    · exact (min_le_right _ _).trans (hsmall Z (lt_of_not_ge hZ₂) hZ)
  · exact (hC Z hZ).trans (le_max_left _ _)

theorem neutral_groundState_exists_of (hgs : type_of% @Packages.groundState_exists)
    (hle : type_of% @Packages.groundEnergy_le) (N : ℕ) :
    ∃ ψ : Wavefunction (N + 1), IsNormalizedGroundState (N + 1) ψ := by
  obtain ⟨ψ, g, hd, hn, he⟩ :=
    hgs (N + 1) (N + 1) (Nat.succ_pos N) le_rfl
  refine ⟨ψ, g, hd, hn, fun χ h hχ hχn => ?_⟩
  rw [he]
  exact hle (N + 1) (N + 1) (Nat.succ_pos N) (Nat.succ_pos N) hχ hχn

theorem halfRadius_le_of_exteriorMass {N : ℕ} (ψ : Wavefunction (N + 1)) {R : ℝ} (hR : 0 ≤ R)
    (h : exteriorMass ψ R ≤ 1 / 2) : halfRadius ψ ≤ R :=
  csInf_le ⟨0, fun _ hr => hr.1⟩ ⟨hR, h⟩

theorem halfRadius_bounds_of (htail : type_of% @Packages.exterior_tail)
    (hlow : type_of% @Packages.radius_lower_large)
    (hfix : type_of% @Packages.radius_bounds_fixed) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ N : ℕ, ∀ ψ : Wavefunction (N + 1),
      IsNormalizedGroundState (N + 1) ψ → c ≤ halfRadius ψ ∧ halfRadius ψ ≤ C := by
  obtain ⟨Ct, R₀, hR₀, Z₃, htail⟩ := htail
  obtain ⟨c, hc, Z₀, hlow⟩ := hlow
  set K := max Z₀ Z₃
  obtain ⟨c₁, hc₁, hsmall⟩ := finite_lower
    (fun N c => ∀ ψ : Wavefunction (N + 1), IsNormalizedGroundState (N + 1) ψ → c ≤ halfRadius ψ)
    (fun _ c c' hcc' h ψ hψ => hcc'.trans (h ψ hψ)) K (fun N _ => by
      obtain ⟨c, C, hc, h⟩ := hfix N
      exact ⟨c, hc, fun ψ hψ => (h ψ hψ).1⟩)
  obtain ⟨C₁, hbig⟩ := finite_upper
    (fun N C => ∀ ψ : Wavefunction (N + 1), IsNormalizedGroundState (N + 1) ψ → halfRadius ψ ≤ C)
    (fun _ C C' hCC' h ψ hψ => (h ψ hψ).trans hCC') K (fun N _ => by
      obtain ⟨c, C, hc, h⟩ := hfix N
      exact ⟨C, fun ψ hψ => (h ψ hψ).2⟩)
  set R := max R₀ (max (2 * Ct) 1)
  have hRpos : 0 < R := lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_right _ _))
  have hRtail : Ct / R ≤ 1 / 2 := by
    rw [div_le_iff₀ hRpos]
    have : 2 * Ct ≤ R := (le_max_left _ _).trans (le_max_right _ _)
    linarith
  refine ⟨min c c₁, max (max R C₁) (min c c₁), lt_min hc hc₁, le_max_right _ _,
    fun N ψ hψ => ⟨?_, ?_⟩⟩
  · by_cases hN : Z₀ ≤ N + 1
    · exact (min_le_left _ _).trans (hlow N hN ψ hψ)
    · exact (min_le_right _ _).trans
        (hsmall N (lt_of_lt_of_le (by omega) (le_max_left _ _)) ψ hψ)
  · refine le_trans ?_ (le_max_left _ _)
    by_cases hN : Z₃ ≤ N + 1
    · exact (halfRadius_le_of_exteriorMass ψ hRpos.le
        ((htail N hN ψ hψ R (le_max_left _ _)).trans hRtail)).trans (le_max_left _ _)
    · exact (hbig N (lt_of_lt_of_le (by omega) (le_max_right _ _)) ψ hψ).trans
        (le_max_right _ _)

/-- `Statement` from the package statements. -/
theorem main_of (hgap : type_of% @Packages.ionization_gap)
    (hupper : type_of% @Packages.ionization_upper) (hbind : type_of% @Packages.binding)
    (hgs : type_of% @Packages.groundState_exists) (hle : type_of% @Packages.groundEnergy_le)
    (htail : type_of% @Packages.exterior_tail) (hlow : type_of% @Packages.radius_lower_large)
    (hfix : type_of% @Packages.radius_bounds_fixed) (hjoint : type_of% @Packages.joint_limit) :
    Statement :=
  ⟨first_ionization_bounds_of hgap hupper hbind, neutral_groundState_exists_of hgs hle,
    halfRadius_bounds_of htail hlow hfix, hjoint⟩

theorem main : Statement :=
  main_of Packages.ionization_gap Packages.ionization_upper Packages.binding
    Packages.groundState_exists Packages.groundEnergy_le Packages.exterior_tail
    Packages.radius_lower_large Packages.radius_bounds_fixed Packages.joint_limit

end AtomicIonization.Blueprint
