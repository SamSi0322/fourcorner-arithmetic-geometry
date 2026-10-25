import PadicUnitNeighbourhood
import LinearizedFieldPoint
import TranscendentalParameters

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
namespace FourCorner.FiniteHenselRealization
open RadicalLinearization PadicUnitNeighbourhood
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

theorem continuous_values (t ki : ℚ_[p]) (i : Fin 5) :
    Continuous (fun l => values t ki l i) := by
  fin_cases i <;> simp only [values] <;> fun_prop

theorem ordinary (hp : p ≠ 2) (t κ : ℚ) (T KI A : ℤ_[p])
    (hT : (T : ℚ_[p]) = t) (hKI : (KI : ℚ_[p]) = (κ : ℚ_[p])⁻¹)
    (r₀ : Fin 5 → ZMod p)
    (hr₀ : ∀ i, r₀ i ^ 2 = values (PadicInt.toZMod T) (PadicInt.toZMod KI) (PadicInt.toZMod A) i)
    (hn : ∀ i, r₀ i ≠ 0) :
    ∃ (e : ℚ_[p]) (r : Fin 5 → ℚ_[p]), Transcendental ℚ e ∧
      ∀ i, r i^2 = values (t : ℚ_[p]) ((κ : ℚ_[p])⁻¹) e i := by
  let f (i : Fin 5) (u : ℚ_[p]) := values (t : ℚ_[p]) ((κ : ℚ_[p])⁻¹) u i
  let a (i : Fin 5) := values T KI A i
  have ha (i : Fin 5) : PadicInt.toZMod (a i) = r₀ i^2 := by
    exact (map_values PadicInt.toZMod T KI A i).trans (hr₀ i).symm
  obtain ⟨e,he,hr⟩ := transcendental_simultaneous_roots hp f A a
    (fun i => (continuous_values _ _ i).continuousAt)
    (fun i => by
      have h := map_values (PadicInt.Coe.ringHom (p := p)) T KI A i
      simpa only [PadicInt.Coe.ringHom_apply,hT,hKI] using h.symm)
    (fun i => by rw [ha]; exact pow_ne_zero _ (hn i))
    (fun i => by rw [ha]; exact IsSquare.sq _)
  choose r hne hs using hr
  exact ⟨e,r,he,hs⟩

/-- One chosen branch root is the free parameter. The other FOUR roots are
lifted simultaneously from their actual nonzero square residues. -/
theorem branch (hp : p ≠ 2) (t κ a b : ℚ) (hb : b ≠ 0) (T KI A : ℤ_[p])
    (hT : (T : ℚ_[p]) = t) (hKI : (KI : ℚ_[p]) = (κ : ℚ_[p])⁻¹)
    (hA : (A : ℚ_[p]) = a) (pivot : Fin 5)
    (hpivot : ∀ u : ℚ_[p], u^2 = values (t : ℚ_[p]) ((κ : ℚ_[p])⁻¹)
      ((a : ℚ_[p])+(b : ℚ_[p])*u^2) pivot)
    (r₀ : Fin 5 → ZMod p)
    (hr₀ : ∀ i, r₀ i ^ 2 = values (PadicInt.toZMod T) (PadicInt.toZMod KI) (PadicInt.toZMod A) i)
    (hn : ∀ i, i ≠ pivot → r₀ i ≠ 0) :
    ∃ (e : ℚ_[p]) (r : Fin 5 → ℚ_[p]), Transcendental ℚ e ∧
      ∀ i, r i^2 = values (t : ℚ_[p]) ((κ : ℚ_[p])⁻¹) e i := by
  let I := {i : Fin 5 // i ≠ pivot}
  let f (i : I) (u : ℚ_[p]) := values (t : ℚ_[p]) ((κ : ℚ_[p])⁻¹)
    ((a : ℚ_[p])+(b : ℚ_[p])*u^2) i.val
  let v (i : I) := values T KI A i.val
  have ha (i : I) : PadicInt.toZMod (v i) = r₀ i.val^2 :=
    (map_values PadicInt.toZMod T KI A i.val).trans (hr₀ i.val).symm
  obtain ⟨u,hu,hr⟩ := transcendental_simultaneous_roots hp f 0 v
    (fun i => (continuous_values _ _ i.val).continuousAt.comp
      (by fun_prop : ContinuousAt (fun u : ℚ_[p] => (a : ℚ_[p])+(b : ℚ_[p])*u^2) 0))
    (fun i => by
      have h := map_values (PadicInt.Coe.ringHom (p := p)) T KI A i.val
      simpa only [PadicInt.Coe.ringHom_apply,hT,hKI,hA,f,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] using h.symm)
    (fun i => by rw [ha]; exact pow_ne_zero _ (hn i.val i.property))
    (fun i => by rw [ha]; exact IsSquare.sq _)
  choose z hz hs using hr
  let r (i : Fin 5) : ℚ_[p] := if h : i=pivot then u else z ⟨i,h⟩
  refine ⟨(a : ℚ_[p])+(b : ℚ_[p])*u^2,r,
    TranscendentalParameters.affine_square hu a b hb,?_⟩
  intro i
  by_cases h : i=pivot
  · subst i
    simpa only [r,dif_pos rfl] using hpivot u
  · simpa only [r,dif_neg h] using hs ⟨i,h⟩

/-- The constructed field solutions give points on the SAME canonical
proper genus17 Q-model. No normalization inverse is assumed. -/
theorem actual_point {t κ : ℚ} (ht : 1<t) (hκ : κ ≠ 0)
    (h : ∃ (e : ℚ_[p]) (r : Fin 5 → ℚ_[p]), Transcendental ℚ e ∧
      ∀ i, r i^2 = values (t : ℚ_[p]) ((κ : ℚ_[p])⁻¹) e i) :
    Nonempty (Spec (CommRingCat.of ℚ_[p]) ⟶
      Genus17Geometry.curve t κ (by linarith) (by linarith) (by linarith)) := by
  obtain ⟨e,r,he,hr⟩ := h
  exact ⟨LinearizedFieldPoint.point t κ ht hκ e he r hr⟩

end FourCorner.FiniteHenselRealization
#print axioms FourCorner.FiniteHenselRealization.ordinary
#print axioms FourCorner.FiniteHenselRealization.branch
#print axioms FourCorner.FiniteHenselRealization.actual_point
