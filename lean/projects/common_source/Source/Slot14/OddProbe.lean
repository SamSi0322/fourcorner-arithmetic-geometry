import ReductionBridge
import Mathlib.GroupTheory.SpecificGroups.Cyclic

noncomputable section
namespace FourCorner.CommonSource.Slot14
open FourCorner.CommonSource

private theorem generator (G : Type*) [AddCommGroup G] (A : G) :
    ∀ x : AddSubgroup.zmultiples A,
      x ∈ AddSubgroup.zmultiples (⟨A, AddSubgroup.mem_zmultiples A⟩ : AddSubgroup.zmultiples A) := by
  intro x
  obtain ⟨k,hk⟩ := x.property
  refine ⟨k,?_⟩
  apply Subtype.ext
  exact hk

noncomputable def coordinate {G : Type*} [AddCommGroup G] (A : G)
    (hA : addOrderOf A = 4) : ZMod 4 ≃+ AddSubgroup.zmultiples A :=
  zmodAddEquivOfGenerator (generator G A) (by rw [Nat.card_zmultiples,hA])

@[simp] theorem coordinate_one {G : Type*} [AddCommGroup G] (A : G)
    (hA : addOrderOf A = 4) : coordinate A hA 1 = ⟨A, AddSubgroup.mem_zmultiples A⟩ :=
  zmodAddEquivOfGenerator_apply_one _ _

variable {q : ℕ} [Fact q.Prime] {n : ℤ}

/-- The probe uses the actual elliptic reduction, restricted to every point of H. -/
noncomputable def phi (H : AddSubgroup (Point (n : ℚ)))
    (hq2 : q ≠ 2) (hnq : (n : ZMod q) ≠ 0)
    (A : ResiduePoint n q) (hA : addOrderOf A = 4)
    (hwhole : ∀ P : H, reduce n hq2 hnq P ∈ AddSubgroup.zmultiples A) : H →+ ZMod 4 :=
  (coordinate A hA).symm.toAddMonoidHom.comp
    (((reduce n hq2 hnq).comp H.subtype).codRestrict _ hwhole)

 theorem phi_spec (H : AddSubgroup (Point (n : ℚ)))
    (hq2 : q ≠ 2) (hnq : (n : ZMod q) ≠ 0)
    (A : ResiduePoint n q) (hA : addOrderOf A = 4)
    (hwhole : ∀ P : H, reduce n hq2 hnq P ∈ AddSubgroup.zmultiples A) (P : H) :
    (coordinate A hA (phi H hq2 hnq A hA hwhole P) : ResiduePoint n q) =
      reduce n hq2 hnq P := by
  simp [phi]
  rfl

 theorem phi_eq_iff (H : AddSubgroup (Point (n : ℚ)))
    (hq2 : q ≠ 2) (hnq : (n : ZMod q) ≠ 0)
    (A : ResiduePoint n q) (hA : addOrderOf A = 4)
    (hwhole : ∀ P : H, reduce n hq2 hnq P ∈ AddSubgroup.zmultiples A) (P Q : H) :
    phi H hq2 hnq A hA hwhole P = phi H hq2 hnq A hA hwhole Q ↔
      reduce n hq2 hnq P = reduce n hq2 hnq Q := by
  constructor
  · intro he
    rw [← phi_spec H hq2 hnq A hA hwhole P,
      ← phi_spec H hq2 hnq A hA hwhole Q, he]
  · intro he
    change (coordinate A hA).symm ⟨reduce n hq2 hnq P,hwhole P⟩ =
      (coordinate A hA).symm ⟨reduce n hq2 hnq Q,hwhole Q⟩
    congr 1
    exact Subtype.ext he

/-- Every element of the full coset W+2H contributes its actual 2φ(Z) term. -/
theorem phi_complete_coset (H : AddSubgroup (Point (n : ℚ)))
    (hq2 : q ≠ 2) (hnq : (n : ZMod q) ≠ 0)
    (A : ResiduePoint n q) (hA : addOrderOf A = 4)
    (hwhole : ∀ P : H, reduce n hq2 hnq P ∈ AddSubgroup.zmultiples A)
    (U V W Z : H) (hcoset : U + V = W + 2 • Z) :
    phi H hq2 hnq A hA hwhole U + phi H hq2 hnq A hA hwhole V =
      phi H hq2 hnq A hA hwhole W + 2 • phi H hq2 hnq A hA hwhole Z := by
  rw [← map_add, hcoset, map_add, map_nsmul]

theorem coordinate_two {G : Type*} [AddCommGroup G] (A : G)
    (hA : addOrderOf A = 4) :
    (coordinate A hA 2 : G) = 2 • A := by
  have htwo : (2 : ZMod 4) = 1 + 1 := by decide
  rw [htwo, map_add, AddSubgroup.coe_add, coordinate_one]
  simp [two_nsmul]

/-- The even cyclic labels are precisely the actual O and T0 reductions. -/
theorem phi_even_labels_iff (H : AddSubgroup (Point (n : ℚ)))
    (hq2 : q ≠ 2) (hnq : (n : ZMod q) ≠ 0)
    (A : ResiduePoint n q) (hA : addOrderOf A = 4)
    (hdouble : 2 • A = residueT0 n hnq)
    (hwhole : ∀ P : H, reduce n hq2 hnq P ∈ AddSubgroup.zmultiples A) (P : H) :
    (phi H hq2 hnq A hA hwhole P = 0 ∨ phi H hq2 hnq A hA hwhole P = 2) ↔
    (reduce n hq2 hnq P = 0 ∨ reduce n hq2 hnq P = residueT0 n hnq) := by
  have hz : (coordinate A hA 0 : ResiduePoint n q) = 0 := by simp
  have ht : (coordinate A hA 2 : ResiduePoint n q) = residueT0 n hnq :=
    (coordinate_two A hA).trans hdouble
  have hinj : Function.Injective (fun z => (coordinate A hA z : ResiduePoint n q)) :=
    Subtype.coe_injective.comp (coordinate A hA).injective
  have hs := phi_spec H hq2 hnq A hA hwhole P
  constructor
  · rintro (h | h)
    · left; rw [← hs, h, hz]
    · right; rw [← hs, h, ht]
  · rintro (h | h)
    · left; apply hinj; exact hs.trans (h.trans hz.symm)
    · right; apply hinj; exact hs.trans (h.trans ht.symm)

/-- A nonsquare abscissa of the actual finite reduction obstructs a square
abscissa in the completed field, without any prescribed valuation depth. -/
theorem nonsquare_abscissa_of_reduction (hq2 : q ≠ 2)
    (hnq : (n : ZMod q) ≠ 0) {x y : ℚ}
    (hcurve : CongruentEquation (n : ℚ) x y) {u v : ZMod q}
    (hred : residueCoordinates (reduce n hq2 hnq
      (finitePoint (rational_ne_zero_of_good hnq) hcurve)) = some (u,v))
    (hu : ¬ IsSquare u) : ¬ IsSquare (x : ℚ_[q]) := by
  intro hs
  obtain ⟨hx, hxu, _⟩ := integral_coordinates_of_reduction_some hq2 hnq hcurve hred
  apply hu
  rw [← hxu]
  exact FourCorner.padicInt_isSquare_toZMod_of_isSquare_coe (rationalIntegral q x hx) hs

end FourCorner.CommonSource.Slot14
#print axioms FourCorner.CommonSource.Slot14.phi_spec
#print axioms FourCorner.CommonSource.Slot14.phi_eq_iff
#print axioms FourCorner.CommonSource.Slot14.phi_complete_coset

#print axioms FourCorner.CommonSource.Slot14.phi_even_labels_iff

#print axioms FourCorner.CommonSource.Slot14.nonsquare_abscissa_of_reduction
