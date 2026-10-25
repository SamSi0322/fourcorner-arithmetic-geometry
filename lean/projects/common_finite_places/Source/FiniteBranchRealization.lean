import FiniteBranchParameters

noncomputable section
namespace FourCorner.FiniteBranchRealization
open FiniteBranchParameters RadicalLinearization
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- All FIVE finite branch charts, including ell=0, use their exact
original rational branch center and a nonzero rational quadratic slope. -/
theorem realize (hp : p ≠ 2) (t κ : ℚ) (ht : 1<t) (hκ : κ ≠ 0)
    (T KI : ℤ_[p]) (hT : (T : ℚ_[p]) = t)
    (hKI : (KI : ℚ_[p]) = (κ : ℚ_[p])⁻¹) (pivot : Fin 5)
    (r₀ : Fin 5 → ZMod p)
    (hr₀ : ∀ i, r₀ i ^ 2 = values (PadicInt.toZMod T) (PadicInt.toZMod KI)
      (center (PadicInt.toZMod T) pivot) i)
    (hn : ∀ i, i ≠ pivot → r₀ i ≠ 0) :
    ∃ (e : ℚ_[p]) (r : Fin 5 → ℚ_[p]), Transcendental ℚ e ∧
      ∀ i, r i^2 = values (t : ℚ_[p]) ((κ : ℚ_[p])⁻¹) e i := by
  have h1 : t ≠ 1 := by linarith
  have hm : t ≠ -1 := by linarith
  have h1p : (t : ℚ_[p]) ≠ 1 := by exact_mod_cast h1
  have hmp : (t : ℚ_[p]) ≠ -1 := by exact_mod_cast hm
  have hκp : (κ : ℚ_[p]) ≠ 0 := by exact_mod_cast hκ
  have hc := center_map (algebraMap ℚ ℚ_[p]) t pivot
  have hs := slope_map (algebraMap ℚ ℚ_[p]) t κ pivot
  simp only [eq_ratCast] at hc hs
  apply FiniteHenselRealization.branch hp t κ (center t pivot) (slope t κ pivot)
    (slope_nonzero t κ h1 hm hκ pivot) T KI (center T pivot) hT hKI
  · have h := center_map (PadicInt.Coe.ringHom (p := p)) T pivot
    simp only [PadicInt.Coe.ringHom_apply] at h
    rw [hT] at h
    exact h.trans hc.symm
  · intro u
    rw [hc,hs]
    exact pivot_equation (t : ℚ_[p]) (κ : ℚ_[p]) h1p hmp hκp pivot u
  · intro i
    have h := center_map PadicInt.toZMod T pivot
    simpa only [h] using hr₀ i
  · exact hn

end FourCorner.FiniteBranchRealization
#print axioms FourCorner.FiniteBranchRealization.realize
