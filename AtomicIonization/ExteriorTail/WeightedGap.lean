import OAI.Analysis.CoulombRadii.SpectralTheory.AmbientEigen
import OAI.Analysis.CoulombRadii.FieldAnalysis.WeightedInner
import OAI.Analysis.CoulombRadii.FieldAnalysis.BodyCoefficient
import OAI.Analysis.CoulombRadii.FieldAnalysis.AtomicWeightGeometry
import OAI.Analysis.CoulombRadii.FieldAnalysis.PotentialAddRsmul

/-!
# The weighted eigen-inequality with an ionization gap

For a ground state `u` of the `n`-electron atom and a smooth bounded one-body coefficient `f`,
testing the eigen-equation with `(∑ᵢ f(xᵢ)²) u` and bounding the energy of the remaining `n - 1`
electrons below by `P ≤ E(n - 1)` gives
`(P - E(n)) 𝔼 ∑ᵢ f(xᵢ)² ≤ ½ 𝔼 ∑ᵢ |∇f(xᵢ)|² + 𝔼 ∑ᵢ f(xᵢ)² B_h(xᵢ)`,
where `B_h(y)` is the field at `y` of the nucleus and the electrons in the ball `|x| < h`.
-/

namespace AtomicIonization.ExteriorTail

open MeasureTheory Filter
open OAI Coulomb

lemma potentialForm_sub {n : ℕ} (u : H1Vector n) (f g : Configuration n → ℝ)
    (hf : ∀ s, Integrable (fun x => f x * ‖u.value s x‖ ^ 2))
    (hg : ∀ s, Integrable (fun x => g x * ‖u.value s x‖ ^ 2)) :
    potentialForm (fun x => f x - g x) u = potentialForm f u - potentialForm g u := by
  unfold potentialForm
  simp only [sub_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  exact integral_sub (hf s) (hg s)

lemma potentialForm_sum_swap {n : ℕ} (u : H1Vector n) (ha : Antisymmetric u)
    (i₀ : Fin n) (F : Fin n → Configuration n → ℝ)
    (hperm : ∀ i x, F i x = F i₀ (permute (Equiv.swap i₀ i) x))
    (hint : ∀ i s, Integrable (fun x => F i x * ‖u.value s x‖ ^ 2)) :
    potentialForm (fun x => ∑ i, F i x) u =
      (n : ℝ) * potentialForm (F i₀) u := by
  rw [potentialForm_finsetSum u Finset.univ F (by intro i hi s; exact hint i s)]
  calc
    _ = ∑ _i : Fin n, potentialForm (F i₀) u := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show F i = fun x => F i₀ (permute (Equiv.swap i₀ i) x) from funext (hperm i)]
      simpa only [potentialForm] using
        (antisymmetric_expectation_permute ha (Equiv.swap i₀ i) (F i₀))
    _ = _ := by simp

lemma weighted_gap_field_integrable (Z : ℕ) (hZ : 1 ≤ Z) {n : ℕ}
    (u : H1Vector n) (f : SmoothBoundedCoefficient) (h : ℝ) (i : Fin n) (s : Spins n) :
    Integrable (fun x => (f.value (position x i)) ^ 2 *
      rawSignedField (attraction (atom Z hZ) (position x i)) (Metric.ball 0 h)
        (position x i) x * ‖u.value s x‖ ^ 2) := by
  let w : Configuration n → ℝ := fun x => (f.value (position x i)) ^ 2
  have hwm : Measurable w := by
    dsimp [w]
    exact (f.smooth.continuous.comp (continuous_position i)).measurable.pow_const 2
  have hwb (x : Configuration n) : ‖w x‖ ≤ f.bound ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hv := f.value_le (position x i)
    nlinarith [f.bound_nonneg, abs_le.mp hv]
  have hA (t : Spins n) : Integrable (fun x : Configuration n =>
      attraction (atom Z hZ) (position x i) * ‖u.value t x‖ ^ 2) := by
    simpa [attraction, atom, Fin.sum_univ_one, sub_zero, mul_assoc] using
      ((u.nuclear_coulomb_integrable_bound t i (0 : Space)
        (by norm_num : (0 : ℝ) < 1)).1.const_mul (Z : ℝ))
  have hR (t : Spins n) : Integrable (fun x : Configuration n =>
      restrictedOutPotential x (Metric.ball 0 h) (position x i) * ‖u.value t x‖ ^ 2) := by
    unfold restrictedOutPotential
    simp only [Finset.sum_mul]
    apply integrable_finsetSum
    intro j hj
    by_cases hij : j = i
    · subst j
      simp only [sub_self, coulombKernel, norm_zero, inv_zero, ite_mul, zero_mul]
      simpa using (integrable_zero : Integrable (fun _ : Configuration n => (0 : ℝ)))
    · have hp := (u.pair_coulomb_integrable_bound t j i hij
        (by norm_num : (0 : ℝ) < 1)).1
      have hset : MeasurableSet {x : Configuration n |
          position x j ∈ Metric.ball (0 : Space) h} :=
        measurableSet_ball.preimage (continuous_position j).measurable
      convert hp.indicator hset using 1
      ext x
      by_cases hx : ‖position x j‖ < h
      · have hxb : position x j ∈ Metric.ball (0 : Space) h := by
          simpa [Metric.mem_ball, dist_zero_right] using hx
        simp [hx, hxb]
      · have hxb : position x j ∉ Metric.ball (0 : Space) h := by
          simpa [Metric.mem_ball, dist_zero_right] using hx
        simp [hx, hxb]
  have hAw : Integrable (fun x : Configuration n =>
      attraction (atom Z hZ) (position x i) * w x * ‖u.value s x‖ ^ 2) :=
    potentialForm_bdd_mul_integrable u _ w hA hwm.aestronglyMeasurable
      (Eventually.of_forall hwb) s
  have hRw : Integrable (fun x : Configuration n =>
      restrictedOutPotential x (Metric.ball 0 h) (position x i) * w x * ‖u.value s x‖ ^ 2) :=
    potentialForm_bdd_mul_integrable u _ w hR hwm.aestronglyMeasurable
      (Eventually.of_forall hwb) s
  have hsub := hAw.sub hRw
  exact hsub.congr (Eventually.of_forall (fun x => by
    dsimp [w, rawSignedField]
    ring))

lemma weighted_gap_one_particle (Z : ℕ) (hZ : 1 ≤ Z) {k : ℕ}
    (u : H1Vector (1 + k)) (ha : Antisymmetric u) (hm : mass u = 1)
    (hmin : (form (atom Z hZ) u : EReal) = sectorFormBottom (atom Z hZ) (1 + k))
    {P : ℝ} (hP : (P : EReal) ≤ sectorFormBottom (atom Z hZ) k)
    (f : SmoothBoundedCoefficient) (h : ℝ) :
    (P - form (atom Z hZ) u) * potentialForm (fun x => (f.value (position x 0)) ^ 2) u ≤
      (1 / 2 : ℝ) * potentialForm (fun x => ∑ b : Fin 3,
        (fderiv ℝ f.value (position x 0) (EuclideanSpace.single b 1)) ^ 2) u +
      potentialForm (fun x => (f.value (position x 0)) ^ 2 *
        rawSignedField (attraction (atom Z hZ) (position x 0)) (Metric.ball 0 h)
          (position x 0) x) u := by
  let F : Configuration (1 + k) → ℝ := fun x => f.value (position x 0)
  let z := u.smoothMul F (f.lift_smooth 0) f.bound f.derivBound
    (fun x => f.value_le (position x 0)) (f.lift_deriv_le 0)
  let v := z.smoothMul F (f.lift_smooth 0) f.bound f.derivBound
    (fun x => f.value_le (position x 0)) (f.lift_deriv_le 0)
  let G : Configuration (1 + k) → ℝ := fun x => ∑ b : Fin 3,
    (fderiv ℝ f.value (position x 0) (EuclideanSpace.single b 1)) ^ 2
  let W : Configuration (1 + k) → ℝ := fun x => (F x) ^ 2
  let d : Fin (1 + k) × Fin 3 → Configuration (1 + k) → ℝ :=
    fun a x => fderiv ℝ F x (EuclideanSpace.single a 1)
  let T : ℝ := (1 / 2 : ℝ) * ∑ s : Spins (1 + k), ∑ a : Fin (1 + k) × Fin 3,
    ∫ x, (d a x) ^ 2 * ‖u.value s x‖ ^ 2
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := f.lift_smooth 0
  have hFb (x : Configuration (1 + k)) : |F x| ≤ f.bound :=
    f.value_le (position x 0)
  have hFd (a : Fin (1 + k) × Fin 3) (x : Configuration (1 + k)) :
      |fderiv ℝ F x (EuclideanSpace.single a 1)| ≤ f.derivBound :=
    f.lift_deriv_le 0 a x
  have hdp (i : Fin (1 + k)) (b : Fin 3) (x : Configuration (1 + k)) :
      d (i, b) x = if i = 0 then
        fderiv ℝ f.value (position x 0) (EuclideanSpace.single b 1) else 0 := by
    dsimp [d, F]
    simpa [eq_comm] using
      (oneBody_derivative f.value f.smooth (0 : Fin (1 + k)) i b x)
  have hpoint (x : Configuration (1 + k)) :
      (∑ a : Fin (1 + k) × Fin 3, (d a x) ^ 2) = G x := by
    classical
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (0 : Fin (1 + k))]
    · simp [G, hdp]
    · intro i hi hne
      simp [hdp, hne]
    · intro hzero
      exact False.elim (hzero (Finset.mem_univ _))
  have hdcont (a : Fin (1 + k) × Fin 3) : Continuous (d a) := by
    dsimp [d]
    exact (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdint (s : Spins (1 + k)) (a : Fin (1 + k) × Fin 3) :
      Integrable (fun x => (d a x) ^ 2 * ‖u.value s x‖ ^ 2) := by
    refine boundedObservable_integrable (B := f.derivBound ^ 2) u _
      ((hdcont a).measurable.pow_const 2) ?_ s
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    have hh := hFd a x
    nlinarith [f.derivBound_nonneg, abs_le.mp hh]
  have hsum (s : Spins (1 + k)) :
      (∑ a : Fin (1 + k) × Fin 3, ∫ x, (d a x) ^ 2 * ‖u.value s x‖ ^ 2) =
        ∫ x, (∑ a : Fin (1 + k) × Fin 3, (d a x) ^ 2) * ‖u.value s x‖ ^ 2 := by
    rw [← integral_finsetSum _ (fun a _ => hdint s a)]
    congr 1
    funext x
    simp only [Finset.sum_mul]
  have hgradAll :
      (∑ s : Spins (1 + k), ∑ a : Fin (1 + k) × Fin 3,
        ∫ x, (d a x) ^ 2 * ‖u.value s x‖ ^ 2) =
        potentialForm (fun x => ∑ a : Fin (1 + k) × Fin 3, (d a x) ^ 2) u := by
    unfold potentialForm
    apply Finset.sum_congr rfl
    intro s hs
    exact hsum s
  have hgradPoint :
      potentialForm (fun x => ∑ a : Fin (1 + k) × Fin 3, (d a x) ^ 2) u =
        potentialForm G u := by
    unfold potentialForm
    apply Finset.sum_congr rfl
    intro s hs
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hpoint]
  have hT : T = (1 / 2 : ℝ) * potentialForm G u := by
    dsimp [T]
    rw [hgradAll, hgradPoint]
  have hdouble := form_double_smoothMul (atom Z hZ) u F hF f.bound f.derivBound
    (fun x => f.value_le (position x 0)) (f.lift_deriv_le 0)
  change form (atom Z hZ) z =
    (form (atom Z hZ) (u.add v) - form (atom Z hZ) u - form (atom Z hZ) v) / 2 + T at hdouble
  have hformPair := formPair_polarization (atom Z hZ) u v
  have hmult : form (atom Z hZ) z = formPair (atom Z hZ) u v + T := by
    rw [hdouble]
    nlinarith [hformPair]
  have heigen := sector_minimizer_ambient_eigen Z hZ u ha hm hmin v
  have hmassDouble := mass_double_smoothMul u F hF f.bound f.derivBound
    (fun x => f.value_le (position x 0)) (f.lift_deriv_le 0)
  change mass z =
    (mass (u.add v) - mass u - mass v) / 2 at hmassDouble
  have hmassPair := massPair_polarization u v
  have hmass : mass z = massPair u v := by linarith [hmassDouble, hmassPair]
  let E : ℝ := form (atom Z hZ) u
  have henergy : form (atom Z hZ) z = E * mass z + T := by
    dsimp [E]
    rw [hmult, heigen, hmass]
  have hanti : ∀ s : Spins 1, ∀ᵐ x, Antisymmetric (z.coreSlice s x) := by
    intro s
    apply z.coreSlice_antisymmetric
    intro p t
    have hFperm (x : Configuration (1 + k)) :
        F (permute (corePerm 1 p) x) = F x := by
      dsimp [F]
      rw [position_permute]
      have H := corePerm_left 1 p (0 : Fin 1)
      change corePerm 1 p 0 = 0 at H
      rw [H]
    filter_upwards [ha (corePerm 1 p) (Fin.append s t)] with x hx
    change (F (permute (corePerm 1 p) x) : ℂ) *
      u.value _ (permute (corePerm 1 p) x) = _
    rw [hFperm x]
    rw [hx]
    change (F x : ℂ) * (_ * u.value _ x) = _ * ((F x : ℂ) * u.value _ x)
    ring
  have hPk : (P : EReal) ≤ sectorFormBottom (atom Z hZ) k := hP
  have hs := slice_core_form_ge_sector (atom Z hZ) z hanti hPk
  change P * mass z ≤ ∑ s : Spins 1, ∫ x,
    mass (z.coreSlice s x) * form (atom Z hZ) (z.coreSlice s x).normalized at hs
  rw [conditional_core_form_identity] at hs
  have hsplit := henergy
  rw [show form (atom Z hZ) z = kinetic z - nuclearEnergy (atom Z hZ) z + pairEnergy z
    from rfl] at hsplit
  rw [kinetic_split, nuclearEnergy_split, pairEnergy_split] at hsplit
  have houterK : 0 ≤ outerKinetic z := by
    unfold outerKinetic
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro s hs
    apply Finset.sum_nonneg
    intro a ha
    exact integral_nonneg (fun x => sq_nonneg _)
  have houterPair :
      0 ≤ potentialForm (fun x => pairPotential ((joinConfiguration 1 k).symm x).1) z := by
    unfold potentialForm
    apply Finset.sum_nonneg
    intro s hs
    apply integral_nonneg
    intro x
    apply mul_nonneg
    · unfold pairPotential
      apply Finset.sum_nonneg
      intro i hi
      apply Finset.sum_nonneg
      intro j hj
      split_ifs <;> first | exact inv_nonneg.mpr (norm_nonneg _) | exact le_rfl
    · positivity
  have houterN := potentialForm_smoothMul u f 0
    (fun x => nuclearPotential (atom Z hZ) ((joinConfiguration 1 k).symm x).1)
  have hcross := potentialForm_smoothMul u f 0
    (fun x => crossPotential ((joinConfiguration 1 k).symm x).1
      ((joinConfiguration 1 k).symm x).2)
  have hcast : Fin.castAdd k (0 : Fin 1) = (0 : Fin (1 + k)) := rfl
  have hball (x : Configuration (1 + k)) :
      restrictedOutPotential x (Metric.ball 0 h) (position x 0) ≤
        crossPotential ((joinConfiguration 1 k).symm x).1 ((joinConfiguration 1 k).symm x).2 := by
    calc
      _ ≤ restrictedOutPotential x Set.univ (position x 0) :=
        restrictedOutPotential_mono x (Set.subset_univ _) (position x 0)
      _ = crossPotential ((joinConfiguration 1 k).symm x).1
          ((joinConfiguration 1 k).symm x).2 := by
        let y := (joinConfiguration 1 k).symm x
        have hy : joinConfiguration 1 k (y.1, y.2) = x :=
          (joinConfiguration 1 k).apply_symm_apply x
        have hpos : position (joinConfiguration 1 k (y.1, y.2))
            (0 : Fin (1 + k)) = position y.1 (0 : Fin 1) := by
          rw [← hcast]
          exact position_join_left y.1 y.2 (0 : Fin 1)
        have hself : restrictedOutPotential y.1 Set.univ (position y.1 0) = 0 := by
          unfold restrictedOutPotential
          apply Finset.sum_eq_zero
          intro i hi
          have hi0 : i = (0 : Fin 1) := Subsingleton.elim _ _
          subst i
          simp [coulombKernel]
        have hcore : restrictedOutPotential y.2 Set.univ (position y.1 0) =
            crossPotential y.1 y.2 := by
          unfold restrictedOutPotential crossPotential
          simp only [Set.mem_univ, ite_true, Fin.sum_univ_one]
          apply Finset.sum_congr rfl
          intro j hj
          exact coulombKernel_sub_comm _ _
        rw [← hy, restrictedOutPotential_join]
        rw [hpos]
        rw [hself, hcore]
        simp
  have hNpoint (x : Configuration (1 + k)) :
      nuclearPotential (atom Z hZ) ((joinConfiguration 1 k).symm x).1 =
        attraction (atom Z hZ) (position x 0) := by
    simp only [nuclearPotential, Fin.sum_univ_one, position_split_left, hcast]
  have hw : ∀ x : Configuration (1 + k), 0 ≤ W x := fun x => sq_nonneg _
  have hWmeas : Measurable W := by
    dsimp [W, F]
    exact (f.smooth.continuous.comp (continuous_position 0)).measurable.pow_const 2
  have hWbound (x : Configuration (1 + k)) : |W x| ≤ f.bound ^ 2 := by
    dsimp [W, F]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [f.bound_nonneg, abs_le.mp (f.value_le (position x 0))]
  have hNint (s : Spins (1 + k)) : Integrable (fun x =>
      nuclearPotential (atom Z hZ) ((joinConfiguration 1 k).symm x).1 *
        ‖u.value s x‖ ^ 2) := u.outer_nuclear_integrable (atom Z hZ) s
  have hNweighted (s : Spins (1 + k)) : Integrable (fun x =>
      nuclearPotential (atom Z hZ) ((joinConfiguration 1 k).symm x).1 * W x *
        ‖u.value s x‖ ^ 2) :=
    potentialForm_bdd_mul_integrable (C := f.bound ^ 2) u _ W hNint
      hWmeas.aestronglyMeasurable
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hWbound x)) s
  have hXint (s : Spins (1 + k)) : Integrable (fun x =>
      crossPotential ((joinConfiguration 1 k).symm x).1
        ((joinConfiguration 1 k).symm x).2 * ‖u.value s x‖ ^ 2) := u.cross_integrable s
  have hXweighted (s : Spins (1 + k)) : Integrable (fun x =>
      crossPotential ((joinConfiguration 1 k).symm x).1
        ((joinConfiguration 1 k).symm x).2 * W x * ‖u.value s x‖ ^ 2) :=
    potentialForm_bdd_mul_integrable (C := f.bound ^ 2) u _ W hXint
      hWmeas.aestronglyMeasurable
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hWbound x)) s
  have hfieldint (s : Spins (1 + k)) := weighted_gap_field_integrable Z hZ u f h 0 s
  have hAweighted (s : Spins (1 + k)) : Integrable (fun x =>
      W x * attraction (atom Z hZ) (position x 0) * ‖u.value s x‖ ^ 2) := by
    exact (hNweighted s).congr (Eventually.of_forall (fun x => by
      change nuclearPotential (atom Z hZ) ((joinConfiguration 1 k).symm x).1 * W x *
        ‖u.value s x‖ ^ 2 = W x * attraction (atom Z hZ) (position x 0) *
          ‖u.value s x‖ ^ 2
      rw [hNpoint x]
      dsimp [W, F]
      ring))
  have hRweighted (s : Spins (1 + k)) : Integrable (fun x =>
      W x * restrictedOutPotential x (Metric.ball 0 h) (position x 0) *
        ‖u.value s x‖ ^ 2) := by
    have hh := (hNweighted s).sub (hfieldint s)
    exact hh.congr (Eventually.of_forall (fun x => by
      change nuclearPotential (atom Z hZ) ((joinConfiguration 1 k).symm x).1 * W x *
          ‖u.value s x‖ ^ 2 -
        f.value (position x 0) ^ 2 *
          rawSignedField (attraction (atom Z hZ) (position x 0))
            (Metric.ball 0 h) (position x 0) x * ‖u.value s x‖ ^ 2 =
        W x * restrictedOutPotential x (Metric.ball 0 h) (position x 0) *
          ‖u.value s x‖ ^ 2
      rw [hNpoint x]
      dsimp [W, F, rawSignedField]
      ring))
  have hXweighted' (s : Spins (1 + k)) : Integrable (fun x =>
      W x * crossPotential ((joinConfiguration 1 k).symm x).1
        ((joinConfiguration 1 k).symm x).2 * ‖u.value s x‖ ^ 2) := by
    exact (hXweighted s).congr (Eventually.of_forall (fun x => by ring))
  have hXle : potentialForm (fun x => W x *
      restrictedOutPotential x (Metric.ball 0 h) (position x 0)) u ≤
      potentialForm (fun x => W x *
        crossPotential ((joinConfiguration 1 k).symm x).1
          ((joinConfiguration 1 k).symm x).2) u := by
    apply potentialForm_mono_ae u _ _ hRweighted hXweighted'
    filter_upwards [] with x
    exact mul_le_mul_of_nonneg_left (hball x) (hw x)
  have hfieldEq : potentialForm (fun x => W x *
      rawSignedField (attraction (atom Z hZ) (position x 0))
        (Metric.ball 0 h) (position x 0) x) u =
      potentialForm (fun x => W x * attraction (atom Z hZ) (position x 0) -
        W x * restrictedOutPotential x (Metric.ball 0 h) (position x 0)) u := by
    congr 1
    funext x
    simp only [rawSignedField]
    ring
  have hNfield : potentialForm
      (fun x => nuclearPotential (atom Z hZ) ((joinConfiguration 1 k).symm x).1) z =
        potentialForm (fun x => W x * attraction (atom Z hZ) (position x 0)) u := by
    rw [houterN]
    congr 1
    funext x
    rw [hNpoint]
    dsimp [W]
    ring
  have hXfield : potentialForm
      (fun x => crossPotential ((joinConfiguration 1 k).symm x).1
        ((joinConfiguration 1 k).symm x).2) z =
        potentialForm (fun x => W x *
          crossPotential ((joinConfiguration 1 k).symm x).1
            ((joinConfiguration 1 k).symm x).2) u := by
    rw [hcross]
    congr 1
    funext x
    dsimp [W]
    ring
  have hloc : (P - E) * potentialForm W u ≤
      (1 / 2 : ℝ) * potentialForm G u +
        potentialForm (fun x => W x *
          rawSignedField (attraction (atom Z hZ) (position x 0))
            (Metric.ball 0 h) (position x 0) x) u := by
    have hraw : (P - E) * mass z ≤ T +
        potentialForm (fun x => nuclearPotential (atom Z hZ)
          ((joinConfiguration 1 k).symm x).1) z -
        potentialForm (fun x => crossPotential ((joinConfiguration 1 k).symm x).1
          ((joinConfiguration 1 k).symm x).2) z := by
      have hsector : P * mass z ≤ coreKinetic z -
          potentialForm (fun x => nuclearPotential (atom Z hZ)
            ((joinConfiguration 1 k).symm x).2) z +
          potentialForm (fun x => pairPotential ((joinConfiguration 1 k).symm x).2) z := hs
      nlinarith [hsplit, hsector, houterK, houterPair]
    have hmassW : mass z = potentialForm W u := by
      calc
        mass z = potentialForm (fun _ => (1 : ℝ)) z := by
          simp [potentialForm_const]
        _ = potentialForm W u := by
          simpa [W, F] using (potentialForm_smoothMul u f 0 (fun _ => (1 : ℝ)))
    have hraw' := hraw
    rw [hmassW, hNfield, hXfield, hT] at hraw'
    have hfieldSub : potentialForm (fun x => W x *
        rawSignedField (attraction (atom Z hZ) (position x 0))
          (Metric.ball 0 h) (position x 0) x) u =
        potentialForm (fun x => W x * attraction (atom Z hZ) (position x 0)) u -
          potentialForm (fun x => W x * restrictedOutPotential x (Metric.ball 0 h)
            (position x 0)) u := by
      calc
        _ = potentialForm (fun x => W x * attraction (atom Z hZ) (position x 0) -
            W x * restrictedOutPotential x (Metric.ball 0 h) (position x 0)) u := hfieldEq
        _ = _ := potentialForm_sub u _ _ hAweighted hRweighted
    rw [hfieldSub]
    linarith [hraw', hXle]
  simpa only [E, W, G] using hloc

theorem weighted_gap_inequality (Z : ℕ) (hZ : 1 ≤ Z) {n : ℕ} (hn : 1 ≤ n) (u : H1Vector n)
    (ha : Antisymmetric u) (hm : mass u = 1)
    (hmin : (form (atom Z hZ) u : EReal) = sectorFormBottom (atom Z hZ) n)
    {P : ℝ} (hP : (P : EReal) ≤ sectorFormBottom (atom Z hZ) (n - 1))
    (f : SmoothBoundedCoefficient) (h : ℝ) :
    (P - form (atom Z hZ) u) * potentialForm (fun x => ∑ i, (f.value (position x i)) ^ 2) u ≤
      (1 / 2 : ℝ) * potentialForm (fun x => ∑ i, ∑ b : Fin 3,
          (fderiv ℝ f.value (position x i) (EuclideanSpace.single b 1)) ^ 2) u +
        potentialForm (weightedInnerField (atom Z hZ) h (fun y => (f.value y) ^ 2)) u := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  let q : Fin (1 + k) → Configuration (1 + k) → ℝ :=
    fun i x => (f.value (position x i)) ^ 2
  let g : Fin (1 + k) → Configuration (1 + k) → ℝ :=
    fun i x => ∑ b : Fin 3,
      (fderiv ℝ f.value (position x i) (EuclideanSpace.single b 1)) ^ 2
  let r : Fin (1 + k) → Configuration (1 + k) → ℝ := fun i x =>
    (f.value (position x i)) ^ 2 *
      rawSignedField (attraction (atom Z hZ) (position x i)) (Metric.ball 0 h)
        (position x i) x
  have hqperm (i : Fin (1 + k)) (x : Configuration (1 + k)) :
      q i x = q 0 (permute (Equiv.swap 0 i) x) := by
    simp [q, position_permute, Equiv.swap_apply_left]
  have hqmeas (i : Fin (1 + k)) : Measurable (q i) := by
    dsimp [q]
    exact (f.smooth.continuous.comp (continuous_position i)).measurable.pow_const 2
  have hqbound (i : Fin (1 + k)) (x : Configuration (1 + k)) :
      |q i x| ≤ f.bound ^ 2 := by
    dsimp [q]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [f.bound_nonneg, abs_le.mp (f.value_le (position x i))]
  have hqint (i : Fin (1 + k)) (s : Spins (1 + k)) :
      Integrable (fun x => q i x * ‖u.value s x‖ ^ 2) :=
    boundedObservable_integrable (B := f.bound ^ 2) u (q i) (hqmeas i) (hqbound i) s
  have hqsum := potentialForm_sum_swap u ha (0 : Fin (1 + k)) q hqperm hqint
  have hgperm (i : Fin (1 + k)) (x : Configuration (1 + k)) :
      g i x = g 0 (permute (Equiv.swap 0 i) x) := by
    simp [g, position_permute, Equiv.swap_apply_left]
  have hgmeas (i : Fin (1 + k)) : Measurable (g i) := by
    dsimp [g]
    apply Finset.measurable_fun_sum
    intro b hb
    exact (((f.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).comp
      (continuous_position i)).measurable.pow_const 2
  have hgbound (i : Fin (1 + k)) (x : Configuration (1 + k)) :
      |g i x| ≤ 3 * f.derivBound ^ 2 := by
    have hnonneg : 0 ≤ g i x := by
      dsimp [g]
      apply Finset.sum_nonneg
      intro b hb
      exact sq_nonneg _
    rw [abs_of_nonneg hnonneg]
    dsimp [g]
    calc
      _ ≤ ∑ _b : Fin 3, f.derivBound ^ 2 := by
        apply Finset.sum_le_sum
        intro b hb
        have hd := f.deriv_le b (position x i)
        nlinarith [f.derivBound_nonneg, abs_le.mp hd]
      _ = 3 * f.derivBound ^ 2 := by simp
  have hgint (i : Fin (1 + k)) (s : Spins (1 + k)) :
      Integrable (fun x => g i x * ‖u.value s x‖ ^ 2) :=
    boundedObservable_integrable (B := 3 * f.derivBound ^ 2) u (g i)
      (hgmeas i) (hgbound i) s
  have hgsum := potentialForm_sum_swap u ha (0 : Fin (1 + k)) g hgperm hgint
  have hrperm (i : Fin (1 + k)) (x : Configuration (1 + k)) :
      r i x = r 0 (permute (Equiv.swap 0 i) x) := by
    simp [r, position_permute, Equiv.swap_apply_left, rawSignedField_permute]
  have hrint (i : Fin (1 + k)) (s : Spins (1 + k)) :
      Integrable (fun x => r i x * ‖u.value s x‖ ^ 2) :=
    weighted_gap_field_integrable Z hZ u f h i s
  have hfieldSum : potentialForm
      (weightedInnerField (atom Z hZ) h (fun y => (f.value y) ^ 2)) u =
        ((1 + k : ℕ) : ℝ) * potentialForm (r 0) u := by
    change potentialForm (fun x => ∑ i : Fin (1 + k), r i x) u = _
    exact potentialForm_sum_swap u ha (0 : Fin (1 + k)) r hrperm hrint
  have hPk : (P : EReal) ≤ sectorFormBottom (atom Z hZ) k := by
    simpa only [Nat.add_sub_cancel_left] using hP
  have hlocal := weighted_gap_one_particle Z hZ u ha hm hmin hPk f h
  have hscale := mul_le_mul_of_nonneg_left hlocal
    (show (0 : ℝ) ≤ ((1 + k : ℕ) : ℝ) by positivity)
  rw [hqsum, hgsum, hfieldSum]
  nlinarith [hscale]

end AtomicIonization.ExteriorTail
