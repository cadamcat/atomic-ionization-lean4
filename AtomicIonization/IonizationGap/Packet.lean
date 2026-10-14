import OAI.Analysis.CoulombRadii.Packets.ScaledWindow
import OAI.Analysis.CoulombRadii.FieldAnalysis.MeridianMap
import OAI.Analysis.CoulombRadii.FormDomain.ParticleGradientNorm
import OAI.Analysis.CoulombRadii.FormDomain.PatchErrors

/-!
# A normalized radial packet and its Coulomb potential

`packetProfile b` is the real radial one-particle packet of radius `b` obtained by rescaling the
unit window; `packetPotential b w` is the Coulomb potential at `w` of its density. Newton's
theorem shows that the packet potential is at most the point potential, with equality outside
the support of the packet.
-/

namespace AtomicIonization.IonizationGap

open OAI OAI.NeutralAtom MeasureTheory
open scoped ContDiff

noncomputable section

/-- The normalized radial packet of radius `b`. -/
def packetProfile (b : ℝ) (v : Position) : ℝ :=
  (Real.sqrt (b ^ 3))⁻¹ * Coulomb.unitWindow (b⁻¹ • v)

/-- The Coulomb potential at `w` of the packet density. -/
def packetPotential (b : ℝ) (w : Position) : ℝ :=
  ∫ v, Coulomb.coulombKernel (w - v) * packetProfile b v ^ 2

/-- The packet translated to the center `y`. -/
def centeredPacket (b : ℝ) (y : Position) (v : Position) : ℝ := packetProfile b (v - y)

theorem packetProfile_eq {b : ℝ} (hb : 0 < b) :
    packetProfile b = fun v => Coulomb.scaledWindow Coulomb.unitWindow b hb.ne' v := by
  funext v
  exact (Coulomb.scaledWindow_apply _ _ _ v).symm

theorem packetProfile_smooth (b : ℝ) : ContDiff ℝ ∞ (packetProfile b) := by
  unfold packetProfile
  exact contDiff_const.mul ((Coulomb.unitWindow.smooth ⊤).comp (contDiff_const_smul b⁻¹))

theorem centeredPacket_smooth (b : ℝ) (y : Position) : ContDiff ℝ ∞ (centeredPacket b y) := by
  unfold centeredPacket
  exact (packetProfile_smooth b).comp (contDiff_id.sub contDiff_const)

theorem centeredPacket_support {b : ℝ} (hb : 0 < b) (y v : Position)
    (hv : centeredPacket b y v ≠ 0) : ‖v - y‖ ≤ b := by
  by_contra h
  apply hv
  unfold centeredPacket
  rw [packetProfile_eq hb]
  exact Coulomb.scaledWindow_support _ Coulomb.unitWindow_support hb _ (lt_of_not_ge h)

theorem centeredPacket_compact {b : ℝ} (hb : 0 < b) (y : Position) :
    HasCompactSupport (centeredPacket b y) := by
  apply HasCompactSupport.intro (K := Metric.closedBall y b) (isCompact_closedBall y b)
  intro v hv
  by_contra h
  exact hv (by simpa [Metric.mem_closedBall, dist_eq_norm] using centeredPacket_support hb y v h)

theorem centeredPacket_memLp {b : ℝ} (hb : 0 < b) (y : Position) :
    MemLp (centeredPacket b y) 2 volume :=
  (centeredPacket_smooth b y).continuous.memLp_of_hasCompactSupport (centeredPacket_compact hb y)

theorem centeredPacket_fderiv_memLp {b : ℝ} (hb : 0 < b) (y : Position) (a : Fin 3) :
    MemLp (fun v => fderiv ℝ (centeredPacket b y) v (EuclideanSpace.single a 1)) 2 volume :=
  (((centeredPacket_smooth b y).continuous_fderiv (by simp)).clm_apply
    continuous_const).memLp_of_hasCompactSupport
    ((centeredPacket_compact hb y).fderiv_apply (𝕜 := ℝ) _)

theorem centeredPacket_fderiv (b : ℝ) (y v : Position) :
    fderiv ℝ (centeredPacket b y) v = fderiv ℝ (packetProfile b) (v - y) := by
  unfold centeredPacket
  exact fderiv_comp_sub (f := packetProfile b) y

theorem centeredPacket_mass {b : ℝ} (hb : 0 < b) (y : Position) :
    (∫ v, centeredPacket b y v ^ 2) = 1 := by
  unfold centeredPacket
  rw [integral_sub_right_eq_self (fun v => packetProfile b v ^ 2) y, packetProfile_eq hb,
    Coulomb.scaledWindow_mass _ hb, Coulomb.unitWindow_mass]

theorem centeredPacket_kinetic {b : ℝ} (hb : 0 < b) (y : Position) :
    oneParticleGradientNorm (centeredPacket b y) = Coulomb.unitWindowKinetic / b ^ 2 := by
  unfold oneParticleGradientNorm
  simp_rw [centeredPacket_fderiv]
  have h (a : Fin 3) := integral_sub_right_eq_self (μ := (volume : Measure Position))
    (fun v => (fderiv ℝ (packetProfile b) v (EuclideanSpace.single a 1)) ^ 2) y
  simp_rw [h, packetProfile_eq hb]
  exact Coulomb.scaledWindow_kinetic _ hb

theorem centeredPacket_fderiv_support {b : ℝ} (hb : 0 < b) (y v : Position)
    (hv : fderiv ℝ (centeredPacket b y) v ≠ 0) : ‖v - y‖ ≤ b := by
  by_contra h
  apply hv
  have he : centeredPacket b y =ᶠ[nhds v] fun _ => (0 : ℝ) := by
    have ho : IsOpen {w : Position | b < ‖w - y‖} :=
      isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
    filter_upwards [ho.mem_nhds (show b < ‖v - y‖ from lt_of_not_ge h)] with w hw
    by_contra hw'
    exact (not_lt_of_ge (centeredPacket_support hb y w hw')) hw
  rw [he.fderiv_eq]
  simp

theorem packetProfile_sq_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun v => packetProfile b v ^ 2) := by
  have h := (centeredPacket_memLp hb 0).integrable_sq
  simpa [centeredPacket] using h

theorem packetProfile_sq_measurable (b : ℝ) : Measurable (fun v => packetProfile b v ^ 2) :=
  ((packetProfile_smooth b).continuous.pow 2).measurable

theorem packetProfile_sq_bounded {b : ℝ} (hb : 0 < b) :
    ∃ M : ℝ, ∀ v, packetProfile b v ^ 2 ≤ M := by
  have hc : HasCompactSupport (fun v => packetProfile b v ^ 2) := by
    have h := (centeredPacket_compact hb 0).mul_left (f := centeredPacket b 0)
    convert h using 1
    funext v
    simp [centeredPacket, sq]
  obtain ⟨C, hC⟩ := ((packetProfile_smooth b).continuous.pow 2).bounded_above_of_compact_support hc
  exact ⟨C, fun v => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC v)⟩

theorem packetProfile_sq_radial {b : ℝ} (hb : 0 < b) (v : Position) :
    packetProfile b v ^ 2 = packetProfile b (EuclideanSpace.single 0 ‖v‖) ^ 2 := by
  rw [packetProfile_eq hb]
  dsimp only
  rw [Coulomb.scaledWindow_radial _ Coulomb.unitWindow_radial hb v]

theorem packetProfile_sq_support {b : ℝ} (hb : 0 < b) (v : Position) (hv : b < ‖v‖) :
    packetProfile b v ^ 2 = 0 := by
  rw [packetProfile_eq hb]
  dsimp only
  rw [Coulomb.scaledWindow_support _ Coulomb.unitWindow_support hb v hv]
  norm_num

theorem packetProfile_sq_mass {b : ℝ} (hb : 0 < b) : (∫ v, packetProfile b v ^ 2) = 1 := by
  simpa [centeredPacket] using centeredPacket_mass hb 0

/-- The nuclear attraction of the centered packet density. -/
theorem centeredPacket_nuclear {b : ℝ} (hb : 0 < b) (y : Position) :
    (∫ v, centeredPacket b y v ^ 2 * ‖v‖⁻¹) = packetPotential b (-y) := by
  unfold packetPotential centeredPacket
  rw [← integral_add_right_eq_self (fun v => packetProfile b (v - y) ^ 2 * ‖v‖⁻¹) y]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [add_sub_cancel_right, Coulomb.coulombKernel]
  rw [show -y - v = -(v + y) by abel, norm_neg]
  ring

/-- The repulsion between the centered packet density and a point charge at `z`. -/
theorem centeredPacket_pair {b : ℝ} (hb : 0 < b) (y z : Position) :
    (∫ v, centeredPacket b y v ^ 2 * ‖v - z‖⁻¹) = packetPotential b (z - y) := by
  unfold packetPotential centeredPacket
  rw [← integral_add_right_eq_self (fun v => packetProfile b (v - y) ^ 2 * ‖v - z‖⁻¹) y]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [add_sub_cancel_right, Coulomb.coulombKernel]
  rw [show z - y - v = -(v + y - z) by abel, norm_neg]
  ring

theorem packetPotential_nonneg (b : ℝ) (w : Position) : 0 ≤ packetPotential b w :=
  integral_nonneg fun v => mul_nonneg (Coulomb.coulombKernel_nonneg _) (sq_nonneg _)

/-- Newton's theorem: the potential of the radial packet is at most the point potential. -/
theorem packetPotential_le {b : ℝ} (hb : 0 < b) {w : Position} (hw : w ≠ 0) :
    packetPotential b w ≤ ‖w‖⁻¹ := by
  obtain ⟨M, hM⟩ := packetProfile_sq_bounded hb
  have H := Coulomb.radial_coulomb_integral_le (packetProfile_sq_integrable hb)
    (packetProfile_sq_measurable b) (fun v => sq_nonneg _) hM (packetProfile_sq_radial hb) hw
  rw [packetProfile_sq_mass hb, mul_one] at H
  exact H

/-- Newton's theorem: outside the packet the potential equals the point potential. -/
theorem packetPotential_eq {b : ℝ} (hb : 0 < b) {w : Position} (hw : b ≤ ‖w‖) :
    packetPotential b w = ‖w‖⁻¹ := by
  obtain ⟨M, hM⟩ := packetProfile_sq_bounded hb
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    linarith
  have H := Coulomb.radial_coulomb_integral_eq (packetProfile_sq_integrable hb)
    (packetProfile_sq_measurable b) (fun v => sq_nonneg _) hM (packetProfile_sq_radial hb) hb.le
    (packetProfile_sq_support hb) hw0 hw
  rw [packetProfile_sq_mass hb, mul_one] at H
  exact H

theorem packetPotential_bounded {b : ℝ} (hb : 0 < b) : ∃ C : ℝ, ∀ w, packetPotential b w ≤ C := by
  obtain ⟨M, hM⟩ := packetProfile_sq_bounded hb
  refine ⟨2 * Real.pi * M * 1 ^ 2 + 1⁻¹ * 1, fun w => ?_⟩
  have H := Coulomb.coulomb_convolution_bound (packetProfile_sq_integrable hb)
    (packetProfile_sq_measurable b) (fun v => sq_nonneg _) hM (by norm_num : (0 : ℝ) < 1) w
  rw [packetProfile_sq_mass hb] at H
  exact H

theorem packetPotential_measurable (b : ℝ) : Measurable (packetPotential b) := by
  have hj : Measurable (fun p : Position × Position =>
      Coulomb.coulombKernel (p.1 - p.2) * packetProfile b p.2 ^ 2) :=
    (Coulomb.coulombKernel_measurable.comp (measurable_fst.sub measurable_snd)).mul
      ((packetProfile_sq_measurable b).comp measurable_snd)
  exact (hj.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure Position))).measurable

end

end AtomicIonization.IonizationGap
