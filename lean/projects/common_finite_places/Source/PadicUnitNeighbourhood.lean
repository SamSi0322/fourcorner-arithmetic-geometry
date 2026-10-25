import PadicTranscendental

noncomputable section
open Filter Topology
namespace FourCorner.PadicUnitNeighbourhood
variable {p : ℕ} [Fact p.Prime]

/-- A unit square residue remains a genuine nonzero Qp square throughout
its entire residue ball, using the actual Hensel theorem. -/
theorem root_of_close (hp : p ≠ 2) (a : ℤ_[p])
    (ha : PadicInt.toZMod a ≠ 0) (hs : IsSquare (PadicInt.toZMod a))
    (x : ℚ_[p]) (hx : ‖x-(a : ℚ_[p])‖ < 1) :
    ∃ z : ℚ_[p], z ≠ 0 ∧ z^2 = x := by
  have hn : ‖x‖ ≤ 1 := by
    calc
      ‖x‖ = ‖(x-(a : ℚ_[p])) + a‖ := by rw [sub_add_cancel]
      _ ≤ max ‖x-(a : ℚ_[p])‖ ‖(a : ℚ_[p])‖ := Padic.nonarchimedean _ _
      _ ≤ 1 := max_le hx.le a.property
  let b : ℤ_[p] := padicIntegral x hn
  have hb : PadicInt.toZMod b = PadicInt.toZMod a := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (padicInt_norm_lt_one_iff_residue_zero (b-a)).mp
    exact hx
  obtain ⟨z,hz,he⟩ := CommonFinitePlaces.lift_unit_square hp b (hb ▸ ha) (hb ▸ hs)
  exact ⟨z,hz,he⟩

/-- Finitely many unit radicands can be lifted SIMULTANEOUSLY at every
parameter in one actual open neighbourhood. -/
theorem eventually_roots {ι : Type*} [Fintype ι]
    (hp : p ≠ 2) (f : ι → ℚ_[p] → ℚ_[p]) (c : ℚ_[p]) (a : ι → ℤ_[p])
    (hf : ∀ i, ContinuousAt (f i) c)
    (he : ∀ i, f i c = (a i : ℚ_[p]))
    (ha : ∀ i, PadicInt.toZMod (a i) ≠ 0)
    (hs : ∀ i, IsSquare (PadicInt.toZMod (a i))) :
    ∀ᶠ u in 𝓝 c, ∀ i, ∃ z : ℚ_[p], z ≠ 0 ∧ z^2 = f i u := by
  apply Filter.eventually_all.mpr
  intro i
  have ht : Tendsto (fun u => ‖f i u-(a i : ℚ_[p])‖) (𝓝 c) (𝓝 0) := by
    have hc : ContinuousAt (fun u => ‖f i u-(a i : ℚ_[p])‖) c :=
      ((hf i).sub (continuousAt_const (y := (a i : ℚ_[p])))).norm
    simpa only [ContinuousAt,he i,sub_self,norm_zero] using hc
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with u hu
  exact root_of_close hp (a i) (ha i) (hs i) (f i u) hu

/-- The simultaneous neighbourhood genuinely contains a Q-transcendental
parameter, so the eventual point can induce a function-field embedding. -/
theorem transcendental_simultaneous_roots {ι : Type*} [Fintype ι]
    (hp : p ≠ 2) (f : ι → ℚ_[p] → ℚ_[p]) (c : ℚ_[p]) (a : ι → ℤ_[p])
    (hf : ∀ i, ContinuousAt (f i) c)
    (he : ∀ i, f i c = (a i : ℚ_[p]))
    (ha : ∀ i, PadicInt.toZMod (a i) ≠ 0)
    (hs : ∀ i, IsSquare (PadicInt.toZMod (a i))) :
    ∃ u : ℚ_[p], Transcendental ℚ u ∧ ∀ i, ∃ z : ℚ_[p], z ≠ 0 ∧ z^2 = f i u := by
  have h := eventually_roots hp f c a hf he ha hs
  obtain ⟨U,hsub,hU,hc⟩ := mem_nhds_iff.mp h
  obtain ⟨u,hu,hT⟩ := PadicTranscendental.exists_in_open hU ⟨c,hc⟩
  exact ⟨u,hT,hsub hu⟩

end FourCorner.PadicUnitNeighbourhood
#print axioms FourCorner.PadicUnitNeighbourhood.root_of_close
#print axioms FourCorner.PadicUnitNeighbourhood.transcendental_simultaneous_roots
