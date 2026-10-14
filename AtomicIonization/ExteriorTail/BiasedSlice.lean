import OAI.Analysis.CoulombRadii.RandomFields.WeightedDeletion

/-!
# Normalized shell-weighted inner field in a recorded ensemble

If every particle carrying shell weight is recorded, the shell-weighted inner field divided by
`ε + ∑ᵢ w(xᵢ)` is, slice by slice, a sub-convex combination of conditional fields at recorded
positions, so its expectation is bounded by the data root mean square of an inner envelope,
with no particle-count factor.
-/

namespace AtomicIonization.ExteriorTail

open OAI Coulomb
open MeasureTheory Set Filter
open scoped BigOperators

lemma normalizedWeightedInnerField_measurable {J n : ℕ} (S : Nuclei J) (h : ℝ)
    {w : Space → ℝ} (hwm : Measurable w) (ε : ℝ) :
    Measurable (fun x : Configuration n =>
      weightedInnerField S h w x / (ε + ∑ i, w (position x i))) := by
  apply (weightedInnerField_measurable S h hwm).div
  apply measurable_const.add
  exact Finset.measurable_sum _ (fun i _ => hwm.comp (continuous_position i).measurable)

lemma normalizedWeightedInnerField_reindex {J m n : ℕ} (S : Nuclei J) (h : ℝ)
    (w : Space → ℝ) (ε : ℝ) (e : Fin m ≃ Fin n) (x : Configuration m) :
    weightedInnerField S h w (reindexConfiguration e x) /
        (ε + ∑ i, w (position (reindexConfiguration e x) i)) =
      weightedInnerField S h w x / (ε + ∑ i, w (position x i)) := by
  have hsum : (∑ i : Fin n, w (position (reindexConfiguration e x) i)) =
      ∑ i : Fin m, w (position x i) := by
    calc
      _ = ∑ i : Fin n, w (position x (e.symm i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [show position (reindexConfiguration e x) i = position x (e.symm i) by
          simpa using position_reindex e x (e.symm i)]
      _ = _ := Equiv.sum_comp e.symm (fun i : Fin m => w (position x i))
  rw [weightedInnerField_reindex, hsum]

lemma normalizedWeightedInnerField_abs_le {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ j, S.position j = 0) {r h : ℝ} (hr : 0 < r) (hh : h ≤ r / 2)
    {w : Space → ℝ} (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∀ y, w y ≤ 1)
    (hws : ∀ y ∉ imsShell 0 r, w y = 0) {ε : ℝ} (hε : 0 < ε) (x : Configuration n) :
    |weightedInnerField S h w x / (ε + ∑ i, w (position x i))| ≤
      ((n : ℝ) * (totalCharge S / r + (n : ℝ) / (r / 2))) / ε := by
  have hwabs (y : Space) : |w y| ≤ 1 := by
    rw [abs_of_nonneg (hw0 y)]
    exact hw1 y
  have hbase := weightedInnerField_abs_le S hatom hr hh hwabs hws x
  let B : ℝ := (n : ℝ) * (totalCharge S / r + (n : ℝ) / (r / 2))
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg
      (div_nonneg (totalCharge_nonneg S) hr.le)
      (div_nonneg (Nat.cast_nonneg _) (by positivity)))
  have hsum (x : Configuration n) : 0 ≤ ∑ i, w (position x i) :=
    Finset.sum_nonneg (fun i _ => hw0 _)
  have hden (x : Configuration n) : 0 < ε + ∑ i, w (position x i) :=
    add_pos_of_pos_of_nonneg hε (hsum x)
  have hden_le (x : Configuration n) : ε ≤ ε + ∑ i, w (position x i) :=
    le_add_of_nonneg_right (hsum x)
  rw [abs_div, abs_of_pos (hden x)]
  calc
    |weightedInnerField S h w x| / (ε + ∑ i, w (position x i)) ≤
        B / (ε + ∑ i, w (position x i)) :=
      div_le_div_of_nonneg_right (by simpa [B] using hbase) (hden x).le
    _ ≤ B / ε := div_le_div_of_nonneg_left hB hε (hden_le x)

lemma conditional_normalized_weighted_inner_le {J m k : ℕ} (S : Nuclei J)
    (hatom : ∀ j, S.position j = 0) (v : H1Vector (m + k))
    {u h : ℝ} (hu : 0 < u) (hh : h ≤ u / 2) {w : Space → ℝ}
    (hwm : Measurable w) (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∀ y, w y ≤ 1)
    (hws : ∀ y ∉ imsShell 0 u, w y = 0) {ε : ℝ} (hε : 0 < ε)
    (s : Spins m) (x : Configuration m) (hm : 0 < mass (v.coreSlice s x))
    (hcore : SpatiallySupported (v.coreSlice s x).normalized (imsShell 0 u)ᶜ)
    {M : ℝ} (hM : 0 ≤ M)
    (hcap : ∀ y, u ≤ ‖y‖ → ‖y‖ ≤ 2 * u →
      max (recordedFarField S (v.coreSlice s x).normalized x (Metric.ball 0 h) y) 0 ≤ M) :
    coreConditionalObservable v (fun z : Configuration (m + k) =>
      weightedInnerField S h w z / (ε + ∑ i, w (position z i))) s x ≤ M := by
  let W' : Configuration (m + k) → ℝ := fun z =>
    weightedInnerField S h w z / (ε + ∑ i, w (position z i))
  change coreConditionalObservable v W' s x ≤ M
  let v₀ := (v.coreSlice s x).normalized
  let sw : ℝ := ∑ i : Fin m, w (position x i)
  let d : ℝ := ε + sw
  let c : ℝ := 1 / d
  have hsw : 0 ≤ sw := Finset.sum_nonneg (fun i _ => hw0 _)
  have hd : 0 < d := by dsimp [d]; linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hWjoin (z : Configuration k) (hz : z ∈ allPositions (imsShell 0 u)ᶜ) :
      W' (joinConfiguration m k (x, z)) =
        c * weightedInnerField S h w (joinConfiguration m k (x, z)) := by
    have hzpos (i : Fin k) : position z i ∉ imsShell 0 u := by
      change ∀ j, position z j ∈ (imsShell 0 u)ᶜ at hz
      exact hz i
    have hweight : (∑ i : Fin (m + k), w
        (position (joinConfiguration m k (x, z)) i)) = sw := by
      simp only [Fin.sum_univ_add, position_join_left, position_join_right]
      have hzsum : (∑ i : Fin k, w (position z i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hws _ (hzpos i)]
      dsimp [sw]
      rw [hzsum, add_zero]
    change weightedInnerField S h w (joinConfiguration m k (x, z)) /
      (ε + ∑ i : Fin (m + k), w
        (position (joinConfiguration m k (x, z)) i)) =
        c * weightedInnerField S h w (joinConfiguration m k (x, z))
    rw [hweight]
    dsimp [c, d]
    ring
  have hcond : coreConditionalObservable v W' s x =
      c * coreConditionalObservable v (weightedInnerField S h w) s x := by
    unfold coreConditionalObservable
    calc
      potentialForm (fun z => W' (joinConfiguration m k (x, z))) v₀ =
          potentialForm (fun z => c * weightedInnerField S h w
            (joinConfiguration m k (x, z))) v₀ := by
        unfold potentialForm
        apply Finset.sum_congr rfl
        intro t ht
        apply integral_congr_ae
        filter_upwards [hcore t] with z hz
        by_cases hsupp : z ∈ allPositions (imsShell 0 u)ᶜ
        · rw [hWjoin z hsupp]
        · rw [hz hsupp]
          simp
      _ = c * coreConditionalObservable v (weightedInnerField S h w) s x :=
        potentialForm_const_mul_value v₀ c _
  let F (i : Fin m) (z : Configuration k) := w (position x i) *
    rawSignedField (attraction S (position x i)) (Metric.ball 0 h) (position x i)
      (joinConfiguration m k (x, z))
  have hwabs (y : Space) : |w y| ≤ 1 := by
    rw [abs_of_nonneg (hw0 y)]
    exact hw1 y
  have hFi (i : Fin m) : Measurable (F i) := (hwm.comp measurable_const).mul
    ((rawSignedField_measurable _ measurableSet_ball _).comp
      ((joinConfiguration m k).continuous.measurable.comp
        (measurable_const.prodMk measurable_id)))
  have hFb (i : Fin m) (z : Configuration k) :
      |F i z| ≤ totalCharge S / u + ((m + k : ℕ) : ℝ) / (u / 2) :=
    weighted_raw_inner_abs_le S hatom hu hh hwabs hws _ _
  have hsum : coreConditionalObservable v (weightedInnerField S h w) s x =
      ∑ i : Fin m, potentialForm (F i) v₀ := by
    unfold coreConditionalObservable potentialForm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    rw [←integral_finsetSum _ (fun i hi => boundedObservable_integrable v₀ (F i)
      (hFi i) (hFb i) q)]
    apply integral_congr_ae
    filter_upwards [hcore q] with z hz
    by_cases hsupp : z ∈ allPositions (imsShell 0 u)ᶜ
    · have hjoin : weightedInnerField S h w (joinConfiguration m k (x, z)) =
          ∑ i : Fin m, F i z := by
        simp only [weightedInnerField, Fin.sum_univ_add, position_join_left, position_join_right]
        have hzsum : (∑ i : Fin k, w (position z i) *
            rawSignedField (attraction S (position z i)) (Metric.ball 0 h)
              (position z i) (joinConfiguration m k (x, z))) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hzi : position z i ∉ imsShell 0 u := by
            change ∀ j, position z j ∈ (imsShell 0 u)ᶜ at hsupp
            exact hsupp i
          rw [hws _ hzi, zero_mul]
        rw [hzsum, add_zero]
      rw [hjoin, Finset.sum_mul]
    · rw [hz hsupp, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
      exact (Finset.sum_eq_zero (fun _ _ => mul_zero _)).symm
  have hnum : coreConditionalObservable v (weightedInnerField S h w) s x ≤ sw * M := by
    rw [hsum]
    calc
      _ ≤ ∑ i : Fin m, w (position x i) * M := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hwi : w (position x i) = 0
        · simp [F, hwi, potentialForm]
        · have hy : position x i ∈ imsShell 0 u := by
            by_contra h
            exact hwi (hws _ h)
          have hyr : u ≤ ‖position x i‖ ∧ ‖position x i‖ ≤ 2 * u := by
            simpa [imsShell] using hy
          have hhf := coreConditionalObservable_rawSignedField v
            (attraction S (position x i)) measurableSet_ball (position x i)
            (show 0 < u / 2 by positivity) (inner_shell_separation hu hh hyr.1) s x hm
          have heq : potentialForm (F i) v₀ = w (position x i) *
              recordedFarField S v₀ x (Metric.ball 0 h) (position x i) := by
            rw [show F i = (fun z => w (position x i) *
              rawSignedField (attraction S (position x i)) (Metric.ball 0 h)
                (position x i) (joinConfiguration m k (x, z))) from rfl,
              potentialForm_const_mul_value]
            exact congrArg (fun z => w (position x i) * z) hhf
          rw [heq]
          exact mul_le_mul_of_nonneg_left
            ((le_max_left _ _).trans (hcap _ hyr.1 hyr.2)) (hw0 _)
      _ = sw * M := by
        dsimp [sw]
        rw [←Finset.sum_mul]
  have hratio : c * sw ≤ 1 := by
    dsimp [c]
    calc
      (1 / d) * sw = sw / d := by ring
      _ ≤ 1 := (div_le_one hd).2 (by dsimp [d]; linarith [hsw])
  rw [hcond]
  calc
    c * coreConditionalObservable v (weightedInnerField S h w) s x ≤ c * (sw * M) :=
      mul_le_mul_of_nonneg_left hnum hc
    _ = (c * sw) * M := by ring
    _ ≤ 1 * M := mul_le_mul_of_nonneg_right hratio hM
    _ = M := one_mul _

theorem normalized_weighted_inner_le {J n : ℕ} (S : Nuclei J) (hatom : ∀ j, S.position j = 0)
    {φ : H1Vector n} {T : RecordedEnsemble n} (hT : T.Conserves φ) (hmass : T.totalMass = 1)
    {r h : ℝ} (hr : 0 < r) (hh : h ≤ r / 2) {w : Space → ℝ} (hwm : Measurable w)
    (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∀ y, w y ≤ 1) (hws : ∀ y ∉ imsShell 0 r, w y = 0)
    (hcore : T.CoreSupported (imsShell 0 r)ᶜ) (M : T.InnerEnvelope S h r)
    {ε : ℝ} (hε : 0 < ε) :
    potentialForm (fun x => weightedInnerField S h w x / (ε + ∑ i, w (position x i))) φ ≤
      T.dataRMS M.value := by
  let W : Configuration n → ℝ := fun x =>
    weightedInnerField S h w x / (ε + ∑ i, w (position x i))
  have hWm : Measurable W := normalizedWeightedInnerField_measurable S h hwm ε
  have hWb (x : Configuration n) :
      |W x| ≤ ((n : ℝ) * (totalCharge S / r + (n : ℝ) / (r / 2))) / ε :=
    normalizedWeightedInnerField_abs_le S hatom hr hh hw0 hw1 hws hε x
  let B : ℝ := ((n : ℝ) * (totalCharge S / r + (n : ℝ) / (r / 2))) / ε
  have hB : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg
      (div_nonneg (totalCharge_nonneg S) hr.le)
      (div_nonneg (Nat.cast_nonneg _) (by positivity)))) hε.le
  have hconservation := hT W hWm ⟨B, fun x => by simpa only [W, B] using hWb x⟩
  have hsumW : (∑ p, potentialForm (fun x : Configuration (T.out p + T.core p) =>
      weightedInnerField S h w x / (ε + ∑ i, w (position x i))) (T.vector p)) =
      potentialForm W φ := by
    simpa only [Function.comp_def, W, normalizedWeightedInnerField_reindex] using hconservation
  have hlocal (p : T.index) :
      potentialForm (fun x : Configuration (T.out p + T.core p) =>
        weightedInnerField S h w x / (ε + ∑ i, w (position x i))) (T.vector p) ≤
        sliceExpectation (T.vector p) (M.value p) := by
    let Wp : Configuration (T.out p + T.core p) → ℝ := fun x =>
      weightedInnerField S h w x / (ε + ∑ i, w (position x i))
    change potentialForm Wp (T.vector p) ≤ sliceExpectation (T.vector p) (M.value p)
    have hWp : Measurable Wp := normalizedWeightedInnerField_measurable S h hwm ε
    have hBp (x : Configuration (T.out p + T.core p)) :
        |Wp x| ≤
          (((T.out p + T.core p : ℕ) : ℝ) *
            (totalCharge S / r + ((T.out p + T.core p : ℕ) : ℝ) / (r / 2))) / ε :=
      normalizedWeightedInnerField_abs_le S hatom hr hh hw0 hw1 hws hε x
    have hbase0 : 0 ≤ ((T.out p + T.core p : ℕ) : ℝ) *
        (totalCharge S / r + ((T.out p + T.core p : ℕ) : ℝ) / (r / 2)) := by
      exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg
        (div_nonneg (totalCharge_nonneg S) hr.le)
        (div_nonneg (Nat.cast_nonneg _) (by positivity)))
    have hB0 : 0 ≤ (((T.out p + T.core p : ℕ) : ℝ) *
        (totalCharge S / r + ((T.out p + T.core p : ℕ) : ℝ) / (r / 2))) / ε := by
      exact div_nonneg hbase0 hε.le
    rw [←sliceExpectation_coreConditionalObservable (T.vector p)
      Wp hWp hBp]
    unfold sliceExpectation
    apply Finset.sum_le_sum
    intro s hs
    apply integral_mono_ae
    · exact coreConditionalObservable_weight_integrable (T.vector p)
        Wp hWp hB0 hBp s
    · exact M.integrable p s
    · have hsupport := (hcore p).coreSlice s
      filter_upwards [hsupport] with x hx
      by_cases hm : mass ((T.vector p).coreSlice s x) = 0
      · simp [hm]
      · have hslice := conditional_normalized_weighted_inner_le S hatom (T.vector p)
          hr hh hwm hw0 hw1 hws hε s x
          (lt_of_le_of_ne (mass_nonneg _) (Ne.symm hm)) hx.normalized
          (M.nonneg p s x) (fun y hy₁ hy₂ => M.dominates p s x y hy₁ hy₂)
        exact mul_le_mul_of_nonneg_left hslice (mass_nonneg _)
  have hsumLocal := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hlocal p)
  rw [hsumW] at hsumLocal
  let R : ℝ := ∑ p, sliceExpectation (T.vector p) (M.value p)
  have hR : 0 ≤ R := by
    dsimp [R]
    apply Finset.sum_nonneg
    intro p hp
    exact Finset.sum_nonneg (fun s _ => integral_nonneg (fun x =>
      mul_nonneg (mass_nonneg _) (M.nonneg p s x)))
  let one : (p : T.index) → Spins (T.out p) → Configuration (T.out p) → ℝ :=
    fun _ _ _ => 1
  have h1 (p : T.index) (s : Spins (T.out p)) :
      Integrable (fun x => mass ((T.vector p).coreSlice s x) * (one p s x) ^ 2) := by
    simpa only [one, one_pow, mul_one] using mass_coreSlice_integrable (T.vector p) s
  have h1M (p : T.index) (s : Spins (T.out p)) :
      Integrable (fun x => mass ((T.vector p).coreSlice s x) * (one p s x * M.value p s x)) := by
    simpa only [one, one_mul] using M.integrable p s
  have hCauchy := slice_ensemble_cauchy T.out T.core T.vector one M.value
    h1 M.square_integrable h1M
  have hmassSum : (∑ p, sliceExpectation (T.vector p) (fun _ _ => (1 : ℝ))) = 1 := by
    calc
      _ = T.totalMass := by
        simp only [sliceExpectation_number, one_mul, RecordedEnsemble.totalMass]
      _ = 1 := hmass
  have hsq : R ^ 2 ≤ T.dataRMS M.value ^ 2 := by
    simpa only [one, one_pow, one_mul, R, hmassSum, ←T.dataRMS_sq] using hCauchy
  have hRle : R ≤ T.dataRMS M.value :=
    (sq_le_sq₀ hR (T.dataRMS_nonneg _)).mp hsq
  calc
    potentialForm W φ ≤ R := by
      simpa only [R] using hsumLocal
    _ ≤ T.dataRMS M.value := hRle

end AtomicIonization.ExteriorTail
