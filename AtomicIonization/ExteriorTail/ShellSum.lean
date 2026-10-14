import OAI.Analysis.CoulombRadii.LimitTheory.NeutralCountControl

/-!
# From shell populations to the exterior mass

Geometric shells `9r/8 ≤ |y| ≤ 15r/8` with ratio `5/3` cover every exterior region, so a bound
`K / r` on the expected shell population gives the bound `3K / R` on the expected number of
electrons outside radius `R`; and the exterior mass of the density of an atomic state is the
expected population of the exterior region.
-/

namespace AtomicIonization.ExteriorTail

open OAI Coulomb
open MeasureTheory

noncomputable def sitePopulationMeasure {n : ℕ} (u : H1Vector n)
    (s : Spins n) (i : Fin n) : Measure Space :=
  Measure.map (fun x : Configuration n => position x i)
    (volume.withDensity (fun x => ENNReal.ofReal (‖u.value s x‖ ^ 2)))

noncomputable def expectedPopulationMeasure {n : ℕ} (u : H1Vector n) : Measure Space :=
  Measure.sum (fun s : Spins n =>
    Measure.sum (fun i : Fin n => sitePopulationMeasure u s i))

lemma sitePopulationMeasure_real {n : ℕ} (u : H1Vector n) (s : Spins n) (i : Fin n)
    {A : Set Space} (hA : MeasurableSet A) :
    (sitePopulationMeasure u s i A).toReal =
      ∫ x, A.indicator (fun _ => (1 : ℝ)) (position x i) * ‖u.value s x‖ ^ 2 := by
  let P : Configuration n → Space := fun x => position x i
  have hP : Measurable P := (continuous_position i).measurable
  have hpre : MeasurableSet (P ⁻¹' A) := hA.preimage hP
  rw [sitePopulationMeasure, Measure.map_apply hP hA, withDensity_apply _ hpre]
  have hnonneg : 0 ≤ᵐ[volume]
      (fun x : Configuration n => A.indicator (fun _ => (1 : ℝ)) (position x i) *
        ‖u.value s x‖ ^ 2) :=
    Filter.Eventually.of_forall fun x =>
      mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (sq_nonneg _)
  have hi := population_integrable u A hA s i
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hi.aestronglyMeasurable]
  congr 1
  rw [← lintegral_indicator hpre]
  congr 1
  funext x
  by_cases hx : position x i ∈ A <;> simp [P, hx]

lemma sitePopulationMeasure_lt_top {n : ℕ} (u : H1Vector n) (s : Spins n) (i : Fin n) :
    sitePopulationMeasure u s i Set.univ < ⊤ := by
  let P : Configuration n → Space := fun x => position x i
  rw [sitePopulationMeasure, Measure.map_apply (continuous_position i).measurable
    MeasurableSet.univ, Set.preimage_univ, withDensity_apply _ MeasurableSet.univ]
  have hi : Integrable (fun x : Configuration n => ‖u.value s x‖ ^ 2) volume :=
    (u.value_L2 s).integrable_norm_pow (by norm_num)
  have hfin := hi.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfin
  apply lt_of_le_of_lt _ hfin
  simpa only [Measure.restrict_univ] using
    (lintegral_mono (μ := volume) (f := fun x => ENNReal.ofReal (‖u.value s x‖ ^ 2))
      (g := fun x => ‖‖u.value s x‖ ^ 2‖ₑ) fun x => by
        have hx : 0 ≤ ‖u.value s x‖ ^ 2 := sq_nonneg _
        simp)

lemma expectedPopulationMeasure_finite {n : ℕ} (u : H1Vector n) :
    IsFiniteMeasure (expectedPopulationMeasure u) := by
  rw [isFiniteMeasure_iff]
  simp only [expectedPopulationMeasure, Measure.sum_apply_of_countable, tsum_fintype]
  apply ENNReal.sum_lt_top.mpr
  intro s hs
  apply ENNReal.sum_lt_top.mpr
  intro i hi
  exact sitePopulationMeasure_lt_top u s i

lemma expectedPopulation_eq_measure_real {n : ℕ} (u : H1Vector n)
    {A : Set Space} (hA : MeasurableSet A) :
    expectedPopulation u A = (expectedPopulationMeasure u).real A := by
  rw [Measure.real_def]
  change expectedPopulation u A =
    ((Measure.sum (fun s : Spins n => Measure.sum
      (fun i : Fin n => sitePopulationMeasure u s i))) A).toReal
  rw [Measure.sum_apply _ hA]
  simp_rw [tsum_fintype, Measure.sum_apply _ hA]
  simp_rw [tsum_fintype]
  rw [expectedPopulation]
  have hsite (s : Spins n) (i : Fin n) : sitePopulationMeasure u s i A ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_mono (Set.subset_univ A)).trans_lt (sitePopulationMeasure_lt_top u s i)
  have hsum (s : Spins n) : (∑ i : Fin n, sitePopulationMeasure u s i A) ≠ ⊤ := by
    apply ne_of_lt
    apply ENNReal.sum_lt_top.mpr
    intro i hi
    exact lt_top_iff_ne_top.mpr (hsite s i)
  rw [ENNReal.toReal_sum (fun s hs => hsum s)]
  apply Finset.sum_congr rfl
  intro s hs
  rw [ENNReal.toReal_sum (fun i hi => hsite s i)]
  apply Finset.sum_congr rfl
  intro i hi
  exact (sitePopulationMeasure_real u s i hA).symm

theorem expectedPopulation_exterior_le {n : ℕ} (u : H1Vector n) {K r₀ : ℝ} (hr₀ : 0 < r₀)
    (hK : 0 ≤ K)
    (hshell : ∀ r : ℝ, r₀ ≤ r →
      expectedPopulation u {y : Space | 9 / 8 * r ≤ ‖y‖ ∧ ‖y‖ ≤ 15 / 8 * r} ≤ K / r) :
    ∀ R : ℝ, 9 / 8 * r₀ ≤ R → expectedPopulation u {y : Space | R < ‖y‖} ≤ 3 * K / R := by
  classical
  intro R hR₀
  have hR : 0 < R := by nlinarith [hr₀, hR₀]
  let q : ℝ := 5 / 3
  let ρ : ℕ → ℝ := fun j => q ^ j * (8 * R / 9)
  let S : ℕ → Set Space := fun j =>
    {y : Space | 9 / 8 * ρ j ≤ ‖y‖ ∧ ‖y‖ ≤ 15 / 8 * ρ j}
  have hρpos (j : ℕ) : 0 < ρ j := by
    dsimp [ρ]
    positivity
  have hρbase : ∀ j : ℕ, r₀ ≤ ρ j := by
    have hbase : r₀ ≤ 8 * R / 9 := by nlinarith
    intro j
    have hq : 1 ≤ q := by norm_num [q]
    have hp : 1 ≤ q ^ j := one_le_pow₀ hq
    dsimp [ρ]
    calc
      r₀ ≤ 8 * R / 9 := hbase
      _ = 1 * (8 * R / 9) := by ring
      _ ≤ q ^ j * (8 * R / 9) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
  have hterm (j : ℕ) : K / ρ j = (9 * K / (8 * R)) * ((3 : ℝ) / 5) ^ j := by
    dsimp [ρ, q]
    field_simp [hR.ne']
    have hrat : ((3 : ℝ) / 5) * (5 / 3) = 1 := by norm_num
    calc
      K = K * ((((3 : ℝ) / 5) * (5 / 3)) ^ j) := by rw [hrat, one_pow, mul_one]
      _ = K * ((3 : ℝ) / 5) ^ j * (5 / 3) ^ j := by rw [mul_pow]; ring
    all_goals ring
  have hpowSummable : Summable (fun j : ℕ => ((3 : ℝ) / 5) ^ j) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hgeomSummable : Summable (fun j : ℕ => K / ρ j) := by
    convert hpowSummable.mul_left (9 * K / (8 * R)) using 1
    ext j
    exact hterm j
  have hgeomEq : (∑' j : ℕ, K / ρ j) = (45 / 16) * K / R := by
    calc
      (∑' j : ℕ, K / ρ j) =
          ∑' j : ℕ, (9 * K / (8 * R)) * ((3 : ℝ) / 5) ^ j :=
        tsum_congr fun j => hterm j
      _ = (9 * K / (8 * R)) * (∑' j : ℕ, ((3 : ℝ) / 5) ^ j) := tsum_mul_left
      _ = (45 / 16) * K / R := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        field_simp [hR.ne']
        ring
  have hgeomBound : (∑' j : ℕ, K / ρ j) ≤ 3 * K / R := by
    rw [hgeomEq]
    have hKR : 0 ≤ K / R := div_nonneg hK hR.le
    calc
      (45 / 16) * K / R = (45 / 16) * (K / R) := by ring
      _ ≤ 3 * (K / R) :=
        mul_le_mul_of_nonneg_right (by norm_num : (45 / 16 : ℝ) ≤ 3) hKR
      _ = 3 * K / R := by ring
  have hcover : {y : Space | R < ‖y‖} ⊆ ⋃ j : ℕ, S j := by
    intro y hy
    have hratio : 1 ≤ ‖y‖ / R := (one_le_div hR).2 (le_of_lt hy)
    obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 5 / 3)
    have hlow : R * ((5 : ℝ) / 3) ^ j ≤ ‖y‖ := by
      have h := (le_div_iff₀ hR).mp hj
      nlinarith [h]
    have hupp : ‖y‖ < R * ((5 : ℝ) / 3) ^ (j + 1) := by
      have h := (div_lt_iff₀ hR).mp hj'
      nlinarith [h]
    have hlowEq : 9 / 8 * ρ j = R * ((5 : ℝ) / 3) ^ j := by
      dsimp [ρ, q]
      ring
    have huppEq : 15 / 8 * ρ j = R * ((5 : ℝ) / 3) ^ (j + 1) := by
      dsimp [ρ, q]
      rw [pow_succ]
      ring
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    constructor
    · rw [hlowEq]
      exact hlow
    · rw [huppEq]
      exact hupp.le
  have hExtMeas : MeasurableSet {y : Space | R < ‖y‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have hSmeas (j : ℕ) : MeasurableSet (S j) := by
    dsimp [S]
    exact (measurableSet_le measurable_const continuous_norm.measurable).inter
      (measurableSet_le continuous_norm.measurable measurable_const)
  let μ : Measure Space := expectedPopulationMeasure u
  have hμfinite : IsFiniteMeasure μ := by
    simpa [μ] using expectedPopulationMeasure_finite u
  have hμuniv : μ Set.univ < ⊤ := by
    rw [isFiniteMeasure_iff] at hμfinite
    exact hμfinite
  have hμExt : μ {y : Space | R < ‖y‖} ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_mono (Set.subset_univ _)).trans_lt hμuniv
  have hμShell (j : ℕ) : μ (S j) ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_mono (Set.subset_univ _)).trans_lt hμuniv
  have hpopExt : expectedPopulation u {y : Space | R < ‖y‖} =
      (μ {y : Space | R < ‖y‖}).toReal := by
    simpa [μ, Measure.real_def] using expectedPopulation_eq_measure_real u hExtMeas
  have hpopShell (j : ℕ) : expectedPopulation u (S j) = (μ (S j)).toReal := by
    simpa [μ, Measure.real_def] using expectedPopulation_eq_measure_real u (hSmeas j)
  have hμShellBound (j : ℕ) : μ (S j) ≤ ENNReal.ofReal (K / ρ j) := by
    rw [← ENNReal.ofReal_toReal (hμShell j), ← hpopShell j]
    exact ENNReal.ofReal_le_ofReal (hshell (ρ j) (hρbase j))
  have hμSumBound : (∑' j : ℕ, μ (S j)) ≤ ∑' j : ℕ, ENNReal.ofReal (K / ρ j) :=
    ENNReal.tsum_le_tsum hμShellBound
  have hμSumFinite : (∑' j : ℕ, μ (S j)) ≠ ⊤ := by
    apply ne_of_lt
    exact (lt_of_le_of_lt hμSumBound hgeomSummable.tsum_ofReal_lt_top)
  have hμCover : μ {y : Space | R < ‖y‖} ≤ ∑' j : ℕ, μ (S j) := by
    calc
      μ {y : Space | R < ‖y‖} ≤ μ (⋃ j : ℕ, S j) := measure_mono hcover
      _ ≤ ∑' j : ℕ, μ (S j) := measure_iUnion_le (μ := μ) S
  have hrealCover : (μ {y : Space | R < ‖y‖}).toReal ≤
      ∑' j : ℕ, (μ (S j)).toReal := by
    have h := (ENNReal.toReal_le_toReal hμExt hμSumFinite).2 hμCover
    rw [ENNReal.tsum_toReal_eq hμShell] at h
    exact h
  have hpopSummable : Summable (fun j : ℕ => expectedPopulation u (S j)) :=
    Summable.of_nonneg_of_le (fun j => expectedPopulation_nonneg u (S j))
      (fun j => hshell (ρ j) (hρbase j)) hgeomSummable
  have hpopCover : expectedPopulation u {y : Space | R < ‖y‖} ≤
      ∑' j : ℕ, expectedPopulation u (S j) := by
    calc
      expectedPopulation u {y : Space | R < ‖y‖} =
          (μ {y : Space | R < ‖y‖}).toReal := hpopExt
      _ ≤ ∑' j : ℕ, (μ (S j)).toReal := hrealCover
      _ = ∑' j : ℕ, expectedPopulation u (S j) :=
        tsum_congr fun j => (hpopShell j).symm
  have hpopGeom : (∑' j : ℕ, expectedPopulation u (S j)) ≤ ∑' j : ℕ, K / ρ j :=
    hpopSummable.tsum_le_tsum (fun j => hshell (ρ j) (hρbase j)) hgeomSummable
  exact hpopCover.trans (hpopGeom.trans hgeomBound)

theorem exteriorMass_eq_expectedPopulation {N : ℕ} {ψ : NeutralAtom.Wavefunction (N + 1)}
    {g : NeutralAtom.Gradient (N + 1)} (hd : NeutralAtom.FormDomain ψ g) (r : ℝ) :
    NeutralAtom.exteriorMass ψ r =
      expectedPopulation (NeutralAtom.asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) {y : Space | r < ‖y‖} := by
  rw [NeutralAtom.exteriorMass]
  have hS : MeasurableSet {y : NeutralAtom.Position | r < ‖y‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  rw [← NeutralAtom.rawExpectation_count_eq_density hd.1 hd.2.2.1 hS,
    ← NeutralAtom.integral_rawLaw hd.2.2.1 (NeutralAtom.rawCount {y : NeutralAtom.Position | r < ‖y‖})]
  exact NeutralAtom.raw_population_asH1 hd hS

end AtomicIonization.ExteriorTail
