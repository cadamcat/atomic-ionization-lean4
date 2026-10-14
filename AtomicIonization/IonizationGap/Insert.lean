import AtomicIonization.IonizationGap.Packet

/-!
# Inserting a packet into a hole of the core

A core state whose particles all stay at distance at least `2b` from a center `y` is wedged with
the normalized packet of radius `b` centered at `y`. The packet and the core occupy disjoint
regions, so the terms assigning different labels to the inserted particle are orthogonal, and the
energy of the antisymmetrized product is the core energy plus the packet kinetic energy minus the
packet-averaged field `insertionField` of the nucleus and the core particles.
-/

namespace AtomicIonization.IonizationGap

open OAI OAI.NeutralAtom MeasureTheory Filter
open scoped ContDiff

noncomputable section

/-- The packet-averaged field at a center `y`: nuclear attraction minus the repulsion of the
particles of the configuration `x`. -/
def insertionField (Z : ℕ) (b : ℝ) (y : Position) {n : ℕ} (x : Configuration n) : ℝ :=
  (Z : ℝ) * packetPotential b (-y) - ∑ i, packetPotential b (x i - y)

/-- The inserted particle lies in the packet ball, while every core particle lies outside it. -/
def BallInsertionSupport {n : ℕ} (b : ℝ) (y : Position) (F : Wavefunction (n+1)) : Prop :=
  ∀ σ x, F σ x ≠ 0 → x 0 ∈ Metric.closedBall y b ∧
    ∀ i : Fin n, x i.succ ∉ Metric.closedBall y b

theorem ballInsertionSupport_tensor {n : ℕ} {b : ℝ} {y : Position}
    (hb : 0 < b) {f : Position → ℝ} {ψ : Wavefunction n}
    (hf : ∀ v, f v ≠ 0 → v ∈ Metric.closedBall y b)
    (hψ : ∀ σ x, ψ σ x ≠ 0 → ∀ i, 2*b ≤ ‖x i-y‖) :
    BallInsertionSupport b y (insertWavefunction f ψ) := by
  intro σ x hx
  have hσ : σ 0 = 0 := by
    by_contra hh
    exact hx (by simp [insertWavefunction, hh])
  have hf0 : f (x 0) ≠ 0 := by
    intro hzero
    exact hx (by simp [insertWavefunction, hσ, hzero])
  have hψ0 : ψ (fun i => σ i.succ) (fun i => x i.succ) ≠ 0 := by
    intro hzero
    exact hx (by simp [insertWavefunction, hσ, hzero])
  refine ⟨hf _ hf0, ?_⟩
  intro i hi
  have hdist := hψ _ _ hψ0 i
  have hb_lt : b < 2*b := by nlinarith
  have hball' : ‖x i.succ-y‖ ≤ b := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hi
  exact (not_le_of_gt (lt_of_lt_of_le hb_lt hdist)) hball'

theorem BallInsertionSupport.swap {n : ℕ} {b : ℝ} {y : Position}
    {F : Wavefunction (n+1)} (hF : BallInsertionSupport b y F)
    {σ : Spins (n+1)} {x : Configuration (n+1)} {i : Fin (n+1)}
    (hi : permuteWavefunction (Equiv.swap 0 i) F σ x ≠ 0) :
    x i ∈ Metric.closedBall y b ∧ ∀ j, j ≠ i → x j ∉ Metric.closedBall y b := by
  have h := hF (σ ∘ Equiv.swap 0 i) (x ∘ Equiv.swap 0 i) hi
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_apply, Equiv.swap_apply_left] using h.1
  · intro j hji
    have hne : Equiv.swap 0 i j ≠ 0 := by
      intro hh
      have he := congrArg (Equiv.swap 0 i) hh
      exact hji (by simpa only [Equiv.swap_apply_self, Equiv.swap_apply_left] using he)
    have hg : ∀ k : Fin (n+1), k ≠ 0 →
        x (Equiv.swap 0 i k) ∉ Metric.closedBall y b := by
      intro k hk
      cases k using Fin.cases with
      | zero => exact (hk rfl).elim
      | succ k => exact h.2 k
    simpa only [Equiv.swap_apply_self] using hg _ hne

theorem BallInsertionSupport.placements_disjoint {n : ℕ} {b : ℝ} {y : Position}
    {F G : Wavefunction (n+1)} (hF : BallInsertionSupport b y F)
    (hG : BallInsertionSupport b y G) (σ : Spins (n+1))
    (x : Configuration (n+1)) {i j : Fin (n+1)} (hij : i ≠ j) :
    permuteWavefunction (Equiv.swap 0 i) F σ x = 0 ∨
      permuteWavefunction (Equiv.swap 0 j) G σ x = 0 := by
  by_contra hh
  have hi := hF.swap (not_or.mp hh).1
  have hj := hG.swap (not_or.mp hh).2
  exact hj.2 i hij hi.1

theorem ballInsertionSupport_gradient {n : ℕ} {b : ℝ} {y : Position}
    (hb : 0 < b)
    {f : Position → ℝ} {ψ : Wavefunction n} {g : Gradient n}
    (hf : ∀ v, f v ≠ 0 → v ∈ Metric.closedBall y b)
    (hdf : ∀ a v, fderiv ℝ f v (EuclideanSpace.single a 1) ≠ 0 →
      v ∈ Metric.closedBall y b)
    (hψ : ∀ σ x, ψ σ x ≠ 0 → ∀ j, 2*b ≤ ‖x j-y‖)
    (hg : ∀ σ i a x, g σ i a x ≠ 0 → ∀ j, 2*b ≤ ‖x j-y‖)
    (i : Fin (n+1)) (a : Fin 3) :
    BallInsertionSupport b y (fun σ x => insertGradient f ψ g σ i a x) := by
  cases i using Fin.cases with
  | zero => exact ballInsertionSupport_tensor hb (hdf a) hψ
  | succ i => exact ballInsertionSupport_tensor hb hf (fun σ x hx => hg σ i a x hx)

theorem inserted_ball_nuclear_bound {n : ℕ} {b : ℝ} {y : Position}
    (hyb : b < ‖y‖) {f : Position → ℝ} {ψ : Wavefunction n}
    (hf : ∀ v, f v ≠ 0 → v ∈ Metric.closedBall y b)
    (σ : Spins (n+1)) (x : Configuration (n+1))
    (hx : insertWavefunction f ψ σ x ≠ 0) :
    |‖x 0‖⁻¹| ≤ (‖y‖-b)⁻¹ := by
  have hσ : σ 0 = 0 := by
    by_contra hh
    exact hx (by simp [insertWavefunction, hh])
  have hf0 : f (x 0) ≠ 0 := by
    intro hzero
    exact hx (by simp [insertWavefunction, hσ, hzero])
  have hball := hf _ hf0
  have hrad : ‖x 0-y‖ ≤ b := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hball
  have hrev : ‖y-x 0‖ ≤ b := by
    calc
      ‖y-x 0‖ = ‖x 0-y‖ := norm_sub_rev _ _
      _ ≤ b := hrad
  have hsep : ‖y‖-b ≤ ‖x 0‖ := by
    have ht := norm_sub_norm_le y (x 0)
    linarith
  have hden : 0 < ‖y‖-b := sub_pos.mpr hyb
  simpa only [one_div, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using
    one_div_le_one_div_of_le hden hsep

theorem inserted_ball_pair_bound {n : ℕ} {b : ℝ} {y : Position}
    (hb : 0 < b) {f : Position → ℝ} {ψ : Wavefunction n}
    (hf : ∀ v, f v ≠ 0 → v ∈ Metric.closedBall y b)
    (hψ : ∀ σ x, ψ σ x ≠ 0 → ∀ j, 2*b ≤ ‖x j-y‖)
    (σ : Spins (n+1)) (x : Configuration (n+1)) (i : Fin n)
    (hx : insertWavefunction f ψ σ x ≠ 0) :
    |‖x 0-x i.succ‖⁻¹| ≤ b⁻¹ := by
  have hσ : σ 0 = 0 := by
    by_contra hh
    exact hx (by simp [insertWavefunction, hh])
  have hf0 : f (x 0) ≠ 0 := by
    intro hzero
    exact hx (by simp [insertWavefunction, hσ, hzero])
  have hψ0 : ψ (fun j => σ j.succ) (fun j => x j.succ) ≠ 0 := by
    intro hzero
    exact hx (by simp [insertWavefunction, hσ, hzero])
  have hball := hf _ hf0
  have hrad : ‖x 0-y‖ ≤ b := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hball
  have hcore := hψ _ _ hψ0 i
  have hsep : b ≤ ‖x 0-x i.succ‖ := by
    have ht := norm_sub_norm_le (x i.succ-y) (x 0-y)
    have heq : (x i.succ-y)-(x 0-y) = x i.succ-x 0 := by abel
    have hrev : ‖x i.succ-x 0‖ = ‖x 0-x i.succ‖ := norm_sub_rev _ _
    rw [heq, hrev] at ht
    linarith
  have hinv := one_div_le_one_div_of_le hb hsep
  simpa only [one_div, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using hinv

theorem FormRegular.insert_ball {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular ψ g) {b : ℝ} {y : Position} (hb : 0 < b) (hyb : b < ‖y‖)
    (hψ : ∀ σ x, ψ σ x ≠ 0 → ∀ i, 2*b ≤ ‖x i-y‖)
    {f : Position → ℝ} (hf : ContDiff ℝ ∞ f) (hfLp : MemLp f 2 volume)
    (hdfLp : ∀ a, MemLp (fun v => fderiv ℝ f v (EuclideanSpace.single a 1)) 2 volume)
    (hfSupport : ∀ v, f v ≠ 0 → v ∈ Metric.closedBall y b) :
    FormRegular (insertWavefunction f ψ) (insertGradient f ψ g) := by
  refine ⟨HasWeakGradient.insert h.1 h.2.1 h.2.2.1 hf hfLp hdfLp,
    insertWavefunction_memLp h.2.1 hfLp,
    insertGradient_memLp h.2.1 h.2.2.1 hfLp hdfLp, ?_, ?_⟩
  · intro σ i
    cases i using Fin.cases with
    | zero =>
      exact integrable_supported_weight (insertWavefunction_memLp h.2.1 hfLp σ)
        (by fun_prop) (inserted_ball_nuclear_bound hyb hfSupport σ)
    | succ i =>
      by_cases hσ : σ 0 = 0
      · simpa only [insertWavefunction, hσ, ↓reduceIte] using
          integrable_weighted_tensor hfLp (h.2.2.2.1 (fun i => σ i.succ) i)
      · simp [insertWavefunction, hσ]
  · intro σ i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hij).elim
      | succ j =>
        exact integrable_supported_weight (insertWavefunction_memLp h.2.1 hfLp σ)
          (by fun_prop) (inserted_ball_pair_bound hb hfSupport hψ σ · j)
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (not_lt_of_ge (Fin.zero_le _) hij).elim
      | succ j =>
        by_cases hσ : σ 0 = 0
        · simpa only [insertWavefunction, hσ, ↓reduceIte] using
            integrable_weighted_tensor hfLp (h.pair (fun i => σ i.succ) i j)
        · simp [insertWavefunction, hσ]

theorem FormRegular.ball_wedgeInsert {n : ℕ} {f : Position → ℝ} {ψ : Wavefunction n}
    {g : Gradient n} (hψ : IsAntisymmetric ψ)
    (h : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g)) :
    FormDomain (wedgeInsert f ψ) (wedgeInsertGradient f ψ g) :=
  ⟨wedgeInsert_antisymmetric hψ f,
    FormRegular.finite_sum (fun i => permutationSign (Equiv.swap 0 i))
      (fun i => h.permute (Equiv.swap 0 i))⟩

theorem normSquared_ballWedgeInsert {n : ℕ} {b : ℝ} {y : Position} {f : Position → ℝ}
    {ψ : Wavefunction n} (hψLp : ∀ σ, MemLp (ψ σ) 2 volume) (hfLp : MemLp f 2 volume)
    (hs : BallInsertionSupport b y (insertWavefunction f ψ)) :
    normSquared (wedgeInsert f ψ) = (n+1 : ℝ) * normSquared (insertWavefunction f ψ) := by
  have hLp (i : Fin (n+1)) (σ : Spins (n+1)) :
      MemLp (permuteWavefunction (Equiv.swap 0 i) (insertWavefunction f ψ) σ) 2 volume :=
    (insertWavefunction_memLp hψLp hfLp _).comp_measurePreserving
      (configurationPerm_preserving (Equiv.swap 0 i))
  unfold wedgeInsert
  rw [normSquared_disjoint_sum _ hLp
    (fun σ x i j hij => hs.placements_disjoint hs σ x hij)]
  simp only [pow_two, permutationSign_sq, one_mul, normSquared_permute, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

theorem energy_ballWedgeInsert {n : ℕ} (Z : ℕ) {b : ℝ} {y : Position}
    {f : Position → ℝ} {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g))
    (hs : BallInsertionSupport b y (insertWavefunction f ψ))
    (hsg : ∀ i a, BallInsertionSupport b y
      (fun σ x => insertGradient f ψ g σ i a x)) :
    energy Z (wedgeInsert f ψ) (wedgeInsertGradient f ψ g) =
      (n+1 : ℝ) * energy Z (insertWavefunction f ψ) (insertGradient f ψ g) := by
  unfold wedgeInsert wedgeInsertGradient
  rw [energy_disjoint_sum Z _ (fun i => h.permute (Equiv.swap 0 i))
    (fun σ x i j hij => hs.placements_disjoint hs σ x hij)
    (fun σ k a x i j hij => (hsg ((Equiv.swap 0 i).symm k) a).placements_disjoint
      (hsg ((Equiv.swap 0 j).symm k) a) σ x hij)]
  simp only [pow_two, permutationSign_sq, one_mul, energy_permute, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

theorem integral_first_weighted_tensor {n : ℕ} (f : Position → ℝ)
    (ψ : Configuration n → ℂ) (W : Position → ℝ) :
    (∫ x : Configuration (n+1), W (x 0) *
      ‖f (x 0) • ψ (fun i => x i.succ)‖^2) =
      (∫ v : Position, W v * (f v)^2) * ∫ x : Configuration n, ‖ψ x‖^2 := by
  have he := (configurationSplit_preserving n).integral_comp
    (configurationSplit n).toHomeomorph.measurableEmbedding
    (fun z : Position × Configuration n => (W z.1*(f z.1)^2)*‖ψ z.2‖^2)
  rw [← integral_prod_mul (μ := volume) (ν := volume)
    (fun v : Position => W v*(f v)^2) (fun x : Configuration n => ‖ψ x‖^2)]
  change _ = ∫ z : Position × Configuration n, (W z.1*(f z.1)^2)*‖ψ z.2‖^2
  rw [← he]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [configurationSplit_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring

theorem weighted_normSquared_insert_first {n : ℕ} (f : Position → ℝ)
    (ψ : Wavefunction n) (W : Position → ℝ) :
    (∑ σ : Spins (n+1), ∫ x : Configuration (n+1),
      W (x 0)*‖insertWavefunction f ψ σ x‖^2) =
      (∫ v : Position, W v*(f v)^2)*normSquared ψ := by
  classical
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Fin 2))]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, insertWavefunction, Fin.cons_zero,
    Fin.cons_succ, h10, ↓reduceIte, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, integral_zero, Finset.sum_const_zero, add_zero,
    integral_first_weighted_tensor, Finset.mul_sum, normSquared]

theorem integrable_pair_packet_tensor {n : ℕ} {b : ℝ} {y : Position}
    (hb : 0 < b) {ψ : Wavefunction n} (hψLp : ∀ σ, MemLp (ψ σ) 2 volume)
    (hψSupport : ∀ σ x, ψ σ x ≠ 0 → ∀ j, 2*b ≤ ‖x j-y‖)
    (σ : Spins n) (i : Fin n) :
    Integrable (fun z : Position × Configuration n =>
      ‖z.1-z.2 i‖⁻¹ *
        ‖centeredPacket b y z.1 • ψ σ z.2‖^2) (volume.prod volume) := by
  have hTensor := memLp_two_real_tensor (centeredPacket_memLp hb y) (hψLp σ)
  apply integrable_supported_weight hTensor (by fun_prop)
  intro z hz
  have hf : centeredPacket b y z.1 ≠ 0 := by
    intro hzero
    apply hz
    simp [hzero]
  have hψ : ψ σ z.2 ≠ 0 := by
    intro hzero
    apply hz
    simp [hzero]
  have hrad := centeredPacket_support hb y z.1 hf
  have hcore := hψSupport σ z.2 hψ i
  have hsep : b ≤ ‖z.1-z.2 i‖ := by
    have ht := norm_sub_norm_le (z.2 i-y) (z.1-y)
    have heq : (z.2 i-y)-(z.1-y) = z.2 i-z.1 := by abel
    have hrev : ‖z.2 i-z.1‖ = ‖z.1-z.2 i‖ := norm_sub_rev _ _
    rw [heq, hrev] at ht
    linarith
  have hinv := one_div_le_one_div_of_le hb hsep
  simpa only [one_div, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using hinv

theorem pair_packet_insert_integral {n : ℕ} {b : ℝ} {y : Position}
    (hb : 0 < b) {ψ : Wavefunction n} (hψLp : ∀ σ, MemLp (ψ σ) 2 volume)
    (hψSupport : ∀ σ x, ψ σ x ≠ 0 → ∀ j, 2*b ≤ ‖x j-y‖)
    (σ : Spins n) (i : Fin n) :
    (∫ x : Configuration (n+1), ‖x 0-x i.succ‖⁻¹ *
      ‖insertWavefunction (centeredPacket b y) ψ (Fin.cons 0 σ) x‖^2) =
      ∫ x : Configuration n, packetPotential b (x i-y)*‖ψ σ x‖^2 := by
  let K : Position × Configuration n → ℝ := fun z =>
    ‖z.1-z.2 i‖⁻¹ * ‖centeredPacket b y z.1 • ψ σ z.2‖^2
  have hK := integrable_pair_packet_tensor hb hψLp hψSupport σ i
  have he := (configurationSplit_preserving n).integral_comp
    (configurationSplit n).toHomeomorph.measurableEmbedding K
  have hinner (x : Configuration n) :
      (∫ v : Position, K (v,x)) = packetPotential b (x i-y)*‖ψ σ x‖^2 := by
    change (∫ v : Position, ‖v-x i‖⁻¹ *
      ‖centeredPacket b y v • ψ σ x‖^2) = _
    calc
      _ = ∫ v : Position,
          ((centeredPacket b y v)^2 * ‖v-x i‖⁻¹) * ‖ψ σ x‖^2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun v => by
          simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
          ring
      _ = (∫ v : Position,
          (centeredPacket b y v)^2 * ‖v-x i‖⁻¹) * ‖ψ σ x‖^2 := by
        rw [integral_mul_const]
      _ = packetPotential b (x i-y)*‖ψ σ x‖^2 := by
        rw [centeredPacket_pair hb y (x i)]
  calc
    _ = ∫ z : Position × Configuration n, K z := by
      calc
        _ = ∫ x : Configuration (n+1), K (configurationSplit n x) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            simp [K, configurationSplit_apply, insertWavefunction]
        _ = ∫ z : Position × Configuration n, K z := he
    _ = ∫ x : Configuration n, ∫ v : Position, K (v,x) :=
      integral_prod_symm K hK
    _ = ∫ x : Configuration n, packetPotential b (x i-y)*‖ψ σ x‖^2 := by
      apply integral_congr_ae
      exact Eventually.of_forall hinner

theorem integral_coulomb_insert_decompose {n : ℕ} (Z : ℕ) {f : Position → ℝ}
    {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular ψ g)
    (hi : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g))
    (hfLp : MemLp f 2 volume) (σ : Spins (n+1)) :
    (∫ x : Configuration (n+1), coulombPotential Z x *
      ‖insertWavefunction f ψ σ x‖^2) =
      (∫ x : Configuration (n+1),
        coulombPotential Z (fun i => x i.succ) * ‖insertWavefunction f ψ σ x‖^2) -
        (Z : ℝ) * (∫ x : Configuration (n+1),
          ‖x 0‖⁻¹ * ‖insertWavefunction f ψ σ x‖^2) +
        ∑ i : Fin n, ∫ x : Configuration (n+1),
          ‖x 0-x i.succ‖⁻¹ * ‖insertWavefunction f ψ σ x‖^2 := by
  by_cases hσ : σ 0 = 0
  · have htail : Integrable (fun x : Configuration (n+1) =>
        coulombPotential Z (fun i => x i.succ) * ‖insertWavefunction f ψ σ x‖^2) := by
      simpa only [insertWavefunction, hσ, ↓reduceIte] using
        integrable_weighted_tensor hfLp (h.integrable_potential Z (fun i => σ i.succ))
    have hnuc := hi.2.2.2.1 σ 0
    have hnucZ : Integrable (fun x : Configuration (n+1) =>
        (Z : ℝ) * (‖x 0‖⁻¹ * ‖insertWavefunction f ψ σ x‖^2)) := hnuc.const_mul _
    have hpair (i : Fin n) : Integrable (fun x : Configuration (n+1) =>
        ‖x 0-x i.succ‖⁻¹ * ‖insertWavefunction f ψ σ x‖^2) :=
      hi.2.2.2.2 σ 0 i.succ (Fin.succ_pos _)
    have hpairSum : Integrable (fun x : Configuration (n+1) =>
        ∑ i : Fin n, ‖x 0-x i.succ‖⁻¹ * ‖insertWavefunction f ψ σ x‖^2) :=
      integrable_finsetSum Finset.univ (fun i _ => hpair i)
    have hpotential (x : Configuration (n+1)) :
        coulombPotential Z x = coulombPotential Z (fun i => x i.succ) -
          (Z : ℝ)*‖x 0‖⁻¹ + ∑ i : Fin n, ‖x 0-x i.succ‖⁻¹ := by
      have hx : x = Fin.cons (x 0) (fun i => x i.succ) := by
        ext i
        cases i using Fin.cases <;> rfl
      rw [hx]
      exact coulombPotential_cons Z (x 0) (fun i => x i.succ)
    calc
      _ = ∫ x : Configuration (n+1),
          (coulombPotential Z (fun i => x i.succ) - (Z : ℝ)*‖x 0‖⁻¹ +
            ∑ i : Fin n, ‖x 0-x i.succ‖⁻¹) *
            ‖insertWavefunction f ψ σ x‖^2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change coulombPotential Z x * ‖insertWavefunction f ψ σ x‖^2 = _
          rw [hpotential x]
      _ = ∫ x : Configuration (n+1),
          (coulombPotential Z (fun i => x i.succ) * ‖insertWavefunction f ψ σ x‖^2 -
            (Z : ℝ) * (‖x 0‖⁻¹ * ‖insertWavefunction f ψ σ x‖^2) +
            ∑ i : Fin n, ‖x 0-x i.succ‖⁻¹ * ‖insertWavefunction f ψ σ x‖^2) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simp only [add_mul, sub_mul, Finset.sum_mul]
          ring
      _ = (∫ x : Configuration (n+1),
            coulombPotential Z (fun i => x i.succ) *
              ‖insertWavefunction f ψ σ x‖^2) -
          (Z : ℝ) * (∫ x : Configuration (n+1),
            ‖x 0‖⁻¹ * ‖insertWavefunction f ψ σ x‖^2) +
          ∑ i : Fin n, ∫ x : Configuration (n+1),
            ‖x 0-x i.succ‖⁻¹ * ‖insertWavefunction f ψ σ x‖^2 := by
        calc
          _ = (∫ x : Configuration (n+1),
                coulombPotential Z (fun i => x i.succ) *
                  ‖insertWavefunction f ψ σ x‖^2 -
                (Z : ℝ) * (‖x 0‖⁻¹ * ‖insertWavefunction f ψ σ x‖^2)) +
              ∫ x : Configuration (n+1),
                ∑ i : Fin n, ‖x 0-x i.succ‖⁻¹ * ‖insertWavefunction f ψ σ x‖^2 := by
            simpa only [Pi.add_apply, Pi.sub_apply] using
              (integral_add (htail.sub hnucZ) hpairSum)
          _ = ((∫ x : Configuration (n+1),
                coulombPotential Z (fun i => x i.succ) *
                  ‖insertWavefunction f ψ σ x‖^2) -
              (∫ x : Configuration (n+1),
                (Z : ℝ) * (‖x 0‖⁻¹ * ‖insertWavefunction f ψ σ x‖^2))) +
              ∫ x : Configuration (n+1),
                ∑ i : Fin n, ‖x 0-x i.succ‖⁻¹ * ‖insertWavefunction f ψ σ x‖^2 := by
            rw [integral_sub htail hnucZ]
          _ = _ := by
            rw [integral_finsetSum Finset.univ (fun i _ => hpair i), integral_const_mul]
  · simp [insertWavefunction, hσ]

theorem pair_packet_tensor_integral {n : ℕ} {b : ℝ} {y : Position}
    (hb : 0 < b) {ψ : Wavefunction n} (hψLp : ∀ σ, MemLp (ψ σ) 2 volume)
    (hψSupport : ∀ σ x, ψ σ x ≠ 0 → ∀ j, 2*b ≤ ‖x j-y‖)
    (σ : Spins n) (i : Fin n) :
    (∫ x : Configuration (n+1), ‖x 0-x i.succ‖⁻¹ *
      ‖centeredPacket b y (x 0) • ψ σ (fun j => x j.succ)‖^2) =
      ∫ x : Configuration n, packetPotential b (x i-y)*‖ψ σ x‖^2 := by
  simpa only [insertWavefunction, Fin.cons_zero, Fin.cons_succ, ↓reduceIte] using
    pair_packet_insert_integral hb hψLp hψSupport σ i

theorem pair_packet_insert_spin_sum {n : ℕ} {b : ℝ} {y : Position}
    (hb : 0 < b) {ψ : Wavefunction n} (hψLp : ∀ σ, MemLp (ψ σ) 2 volume)
    (hψSupport : ∀ σ x, ψ σ x ≠ 0 → ∀ j, 2*b ≤ ‖x j-y‖) :
    (∑ σ : Spins (n+1), ∑ i : Fin n, ∫ x : Configuration (n+1),
      ‖x 0-x i.succ‖⁻¹ *
        ‖insertWavefunction (centeredPacket b y) ψ σ x‖^2) =
    ∑ σ : Spins n, ∑ i : Fin n, ∫ x : Configuration n,
      packetPotential b (x i-y)*‖ψ σ x‖^2 := by
  classical
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Fin 2))]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ, h10,
    ↓reduceIte, insertWavefunction]
  simp_rw [pair_packet_tensor_integral hb hψLp hψSupport]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, integral_zero,
    Finset.sum_const_zero, add_zero]

theorem integrable_packet_potential_weight {n : ℕ} {b : ℝ} {y : Position}
    (hb : 0 < b) {ψ : Configuration n → ℂ} (hψ : MemLp ψ 2 volume)
    (i : Fin n) :
    Integrable (fun x : Configuration n =>
      packetPotential b (x i-y)*‖ψ x‖^2) volume := by
  obtain ⟨C, hC⟩ := packetPotential_bounded hb
  apply integrable_supported_weight hψ
    ((packetPotential_measurable b).comp (by fun_prop))
  intro x hx
  calc
    |packetPotential b (x i-y)| = packetPotential b (x i-y) :=
      abs_of_nonneg (packetPotential_nonneg b _)
    _ ≤ C := hC _

theorem integral_insertionField_single {n : ℕ} (Z : ℕ) {b : ℝ} {y : Position}
    (hb : 0 < b) {ψ : Wavefunction n} (hψLp : ∀ σ, MemLp (ψ σ) 2 volume)
    (σ : Spins n) :
    (∫ x : Configuration n, insertionField Z b y x*‖ψ σ x‖^2) =
      ((Z : ℝ)*packetPotential b (-y)) *
        (∫ x : Configuration n, ‖ψ σ x‖^2) -
      ∑ i : Fin n, (∫ x : Configuration n,
        packetPotential b (x i-y)*‖ψ σ x‖^2) := by
  have hnorm : Integrable (fun x : Configuration n => ‖ψ σ x‖^2) :=
    (hψLp σ).norm.integrable_sq
  have hconst : Integrable (fun x : Configuration n =>
      ((Z : ℝ)*packetPotential b (-y))*‖ψ σ x‖^2) := hnorm.const_mul _
  have hpair (i : Fin n) : Integrable (fun x : Configuration n =>
      packetPotential b (x i-y)*‖ψ σ x‖^2) :=
    integrable_packet_potential_weight hb (hψLp σ) i
  have hpairSum : Integrable (fun x : Configuration n =>
      ∑ i : Fin n, packetPotential b (x i-y)*‖ψ σ x‖^2) :=
    integrable_finsetSum Finset.univ (fun i _ => hpair i)
  calc
    _ = ∫ x : Configuration n,
        (((Z : ℝ)*packetPotential b (-y))*‖ψ σ x‖^2 -
          ∑ i : Fin n, packetPotential b (x i-y)*‖ψ σ x‖^2) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [insertionField]
        rw [sub_mul]
        have hsum :
            (∑ i : Fin n, packetPotential b (x i-y))*‖ψ σ x‖^2 =
            ∑ i : Fin n, packetPotential b (x i-y)*‖ψ σ x‖^2 := by
          rw [Finset.sum_mul]
        rw [hsum]
    _ = (∫ x : Configuration n,
          ((Z : ℝ)*packetPotential b (-y))*‖ψ σ x‖^2) -
        ∫ x : Configuration n,
          ∑ i : Fin n, packetPotential b (x i-y)*‖ψ σ x‖^2 :=
      integral_sub hconst hpairSum
    _ = ((Z : ℝ)*packetPotential b (-y)) *
          (∫ x : Configuration n, ‖ψ σ x‖^2) -
        ∑ i : Fin n, (∫ x : Configuration n,
          packetPotential b (x i-y)*‖ψ σ x‖^2) := by
      rw [integral_const_mul,
        integral_finsetSum Finset.univ (fun i _ => hpair i)]

theorem insertionField_spin_sum {n : ℕ} (Z : ℕ) {b : ℝ} {y : Position}
    (hb : 0 < b) {ψ : Wavefunction n} (hψLp : ∀ σ, MemLp (ψ σ) 2 volume) :
    (∑ σ : Spins n, ∫ x : Configuration n,
      insertionField Z b y x*‖ψ σ x‖^2) =
      ((Z : ℝ)*packetPotential b (-y))*normSquared ψ -
        ∑ σ : Spins n, ∑ i : Fin n, ∫ x : Configuration n,
          packetPotential b (x i-y)*‖ψ σ x‖^2 := by
  classical
  simp_rw [integral_insertionField_single Z hb hψLp]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  change ((Z : ℝ)*packetPotential b (-y)) *
      (∑ σ : Spins n, ∫ x : Configuration n, ‖ψ σ x‖^2) -
      ∑ σ : Spins n, ∑ i : Fin n, ∫ x : Configuration n,
        packetPotential b (x i-y)*‖ψ σ x‖^2 = _
  rfl

theorem potentialForm_centered_insert_exact {n : ℕ} (Z : ℕ) {b : ℝ} {y : Position}
    (hb : 0 < b) {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular ψ g)
    (hi : FormRegular (insertWavefunction (centeredPacket b y) ψ)
      (insertGradient (centeredPacket b y) ψ g))
    (hψSupport : ∀ σ x, ψ σ x ≠ 0 → ∀ i, 2*b ≤ ‖x i-y‖) :
    potentialForm Z (insertWavefunction (centeredPacket b y) ψ) =
      potentialForm Z ψ -
        ∑ σ : Spins n, ∫ x : Configuration n,
          insertionField Z b y x*‖ψ σ x‖^2 := by
  classical
  have hmass := centeredPacket_mass hb y
  have hnuclear : (∫ v : Position,
      ‖v‖⁻¹*(centeredPacket b y v)^2) = packetPotential b (-y) := by
    calc
      _ = ∫ v : Position, (centeredPacket b y v)^2*‖v‖⁻¹ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun v => by ring
      _ = packetPotential b (-y) := centeredPacket_nuclear hb y
  have hdecompSum :
      (∑ σ : Spins (n+1), ∫ x : Configuration (n+1),
        coulombPotential Z x *
          ‖insertWavefunction (centeredPacket b y) ψ σ x‖^2) =
      (∑ σ : Spins (n+1), ∫ x : Configuration (n+1),
        coulombPotential Z (fun i => x i.succ) *
          ‖insertWavefunction (centeredPacket b y) ψ σ x‖^2) -
      (Z : ℝ) * (∑ σ : Spins (n+1), ∫ x : Configuration (n+1),
        ‖x 0‖⁻¹ * ‖insertWavefunction (centeredPacket b y) ψ σ x‖^2) +
      (∑ σ : Spins (n+1), ∑ i : Fin n, ∫ x : Configuration (n+1),
        ‖x 0-x i.succ‖⁻¹ *
          ‖insertWavefunction (centeredPacket b y) ψ σ x‖^2) := by
    simp_rw [integral_coulomb_insert_decompose Z h hi (centeredPacket_memLp hb y)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  calc
    potentialForm Z (insertWavefunction (centeredPacket b y) ψ) =
        potentialForm Z ψ -
          ∑ σ : Spins n, ∫ x : Configuration n,
            insertionField Z b y x*‖ψ σ x‖^2 := by
      change (∑ σ : Spins (n+1), ∫ x : Configuration (n+1),
        coulombPotential Z x *
          ‖insertWavefunction (centeredPacket b y) ψ σ x‖^2) = _
      rw [hdecompSum]
      rw [weighted_normSquared_insert (centeredPacket b y) ψ
        (fun x => coulombPotential Z x)]
      rw [weighted_normSquared_insert_first (centeredPacket b y) ψ
        (fun v => ‖v‖⁻¹)]
      rw [pair_packet_insert_spin_sum hb h.2.1 hψSupport]
      rw [hmass, hnuclear]
      rw [insertionField_spin_sum Z hb h.2.1]
      unfold potentialForm
      ring

theorem energy_centered_insert_exact {n : ℕ} (Z : ℕ) {b : ℝ} {y : Position}
    (hb : 0 < b) {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular ψ g)
    (hi : FormRegular (insertWavefunction (centeredPacket b y) ψ)
      (insertGradient (centeredPacket b y) ψ g))
    (hψSupport : ∀ σ x, ψ σ x ≠ 0 → ∀ i, 2*b ≤ ‖x i-y‖) :
    energy Z (insertWavefunction (centeredPacket b y) ψ)
        (insertGradient (centeredPacket b y) ψ g) =
      energy Z ψ g + (1/2 : ℝ) *
        (Coulomb.unitWindowKinetic / b^2)*normSquared ψ -
        ∑ σ : Spins n, ∫ x : Configuration n,
          insertionField Z b y x*‖ψ σ x‖^2 := by
  rw [energy_decompose, energy_decompose, gradientNormSquared_insert,
    centeredPacket_mass hb y, centeredPacket_kinetic hb y,
    potentialForm_centered_insert_exact Z hb h hi hψSupport]
  ring

/-- Insertion of the centered packet into a core state supported away from the center. -/
theorem ball_insertion (Z : ℕ) {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {y : Position} {b : ℝ} (hb : 0 < b) (hyb : b < ‖y‖)
    (hψ : ∀ σ x, ψ σ x ≠ 0 → ∀ i, 2 * b ≤ ‖x i - y‖)
    (hg : ∀ σ i a x, g σ i a x ≠ 0 → ∀ j, 2 * b ≤ ‖x j - y‖)
    (hpos : 0 < normSquared ψ) :
    ∃ (χ : Wavefunction (n + 1)) (h : Gradient (n + 1)),
      FormDomain χ h ∧ normSquared χ = 1 ∧
      energy Z χ h * normSquared ψ ≤ energy Z ψ g +
        (1 / 2 : ℝ) * (Coulomb.unitWindowKinetic / b ^ 2) * normSquared ψ -
        ∑ σ, ∫ x, insertionField Z b y x * ‖ψ σ x‖ ^ 2 := by
  let f : Position → ℝ := centeredPacket b y
  have hfLp : MemLp f 2 volume := by
    exact centeredPacket_memLp hb y
  have hdfLp (a : Fin 3) :
      MemLp (fun v => fderiv ℝ f v (EuclideanSpace.single a 1)) 2 volume := by
    exact centeredPacket_fderiv_memLp hb y a
  have hfSupport : ∀ v, f v ≠ 0 → v ∈ Metric.closedBall y b := by
    intro v hv
    have hs := centeredPacket_support hb y v hv
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hs
  have hdfSupport : ∀ a v,
      fderiv ℝ f v (EuclideanSpace.single a 1) ≠ 0 →
        v ∈ Metric.closedBall y b := by
    intro a v hv
    have hv' : fderiv ℝ (centeredPacket b y) v (EuclideanSpace.single a 1) ≠ 0 := by
      simpa only [f] using hv
    have hmap : fderiv ℝ (centeredPacket b y) v ≠ 0 := by
      intro hzero
      apply hv'
      rw [hzero]
      simp
    have hs := centeredPacket_fderiv_support hb y v hmap
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hs
  have hi : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g) :=
    FormRegular.insert_ball hd.2 hb hyb hψ
      (centeredPacket_smooth b y) hfLp hdfLp hfSupport
  have hs : BallInsertionSupport b y (insertWavefunction f ψ) :=
    ballInsertionSupport_tensor hb hfSupport hψ
  have hsg : ∀ i a, BallInsertionSupport b y
      (fun σ x => insertGradient f ψ g σ i a x) := by
    intro i a
    exact ballInsertionSupport_gradient hb hfSupport hdfSupport hψ hg i a
  have hden : 0 < (n+1 : ℝ)*normSquared ψ := by positivity
  let c : ℝ := (Real.sqrt ((n+1 : ℝ)*normSquared ψ))⁻¹
  have hc : c^2*((n+1 : ℝ)*normSquared ψ) = 1 := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt hden.le]
    exact inv_mul_cancel₀ hden.ne'
  refine ⟨scaleWavefunction c (wedgeInsert f ψ),
    scaleGradient c (wedgeInsertGradient f ψ g), ?_, ?_, ?_⟩
  · exact (FormRegular.ball_wedgeInsert hd.1 hi).scale c
  · rw [normSquared_scale, normSquared_ballWedgeInsert hd.2.2.1 hfLp hs,
      normSquared_insert, centeredPacket_mass hb y]
    simpa only [one_mul] using hc
  · rw [energy_scale, energy_ballWedgeInsert Z hi hs hsg]
    calc
      c^2*((n+1 : ℝ)*energy Z (insertWavefunction f ψ) (insertGradient f ψ g)) *
          normSquared ψ = energy Z (insertWavefunction f ψ) (insertGradient f ψ g) := by
        calc
          _ = (c^2*((n+1 : ℝ)*normSquared ψ)) *
              energy Z (insertWavefunction f ψ) (insertGradient f ψ g) := by ring
          _ = _ := by rw [hc, one_mul]
      _ ≤ energy Z ψ g + (1/2 : ℝ) *
          (Coulomb.unitWindowKinetic / b^2)*normSquared ψ -
          ∑ σ, ∫ x, insertionField Z b y x*‖ψ σ x‖^2 := by
        rw [energy_centered_insert_exact Z hb hd.2 hi hψ]

end

end AtomicIonization.IonizationGap
