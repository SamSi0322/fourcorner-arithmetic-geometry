import HpNativeBranchEquivalence
import HpFamilyConstituents
import ThetaIsoFunctionField
import Mathlib.Data.Fintype.Pigeonhole

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace FourCorner.HpGeometricIsoFibres
open AlgebraicGeometry CategoryTheory AlgebraicCurve
noncomputable section
attribute [local instance] Classical.propDecidable
abbrev K := AlgebraicClosure ℚ
abbrev Parameter := {p : ℚ // 1<p}

def geometricObject (p : Parameter) : Over (Spec (CommRingCat.of K)) :=
  Over.mk (HpSchemeModel.geometricToBase p.val)

def literalFieldEquiv {p q : ℚ} (hp : 1<p) (hq : 1<q)
    (e : HpSchemeModel.geometricScheme p ≅ HpSchemeModel.geometricScheme q)
    (he : e.hom ≫ HpSchemeModel.geometricToBase q=HpSchemeModel.geometricToBase p) :
    HpLiteralField.field K (algebraMap ℚ K p) ≃ₐ[K] HpLiteralField.field K (algebraMap ℚ K q) := by
  letI := HpSchemeModel.geometricIntegral p hp
  letI := HpSchemeModel.geometricIntegral q hq
  letI := (baseToFunctionField (HpSchemeModel.geometricToBase p)).toAlgebra
  letI := (baseToFunctionField (HpSchemeModel.geometricToBase q)).toAlgebra
  exact (HpSchemeModel.geometricFieldEquiv p hp).trans
    ((ThetaIsoFunctionField.algEquiv (HpSchemeModel.geometricToBase p) (HpSchemeModel.geometricToBase q) e he).symm.trans
      (HpSchemeModel.geometricFieldEquiv q hq).symm)

def geometricSetoid : Setoid Parameter where
  r p q := Nonempty (geometricObject p ≅ geometricObject q)
  iseqv := ⟨fun p => ⟨Iso.refl _⟩,fun ⟨e⟩ => ⟨e.symm⟩,fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

theorem branch_equivalent_of_geometric_iso {p q : Parameter}
    (h : geometricSetoid.r p q) :
    HasseRationalBranchFiniteness.rationalEquivalent (K := K) p.val q.val := by
  obtain ⟨e⟩ := h
  let ec : HpSchemeModel.geometricScheme p.val ≅ HpSchemeModel.geometricScheme q.val :=
    (Over.forget _).mapIso e
  have he : ec.hom ≫ HpSchemeModel.geometricToBase q.val=HpSchemeModel.geometricToBase p.val := by
    change e.hom.left ≫ HpSchemeModel.geometricToBase q.val=HpSchemeModel.geometricToBase p.val
    exact e.hom.w
  apply HpNativeBranchEquivalence.equivalent_of_field_iso K (literalFieldEquiv p.property q.property ec he)
  · exact (map_ne_zero (algebraMap ℚ K)).mpr (show p.val ≠ 0 by linarith [p.property])
  · simpa only [map_sub,map_one] using (map_ne_zero (algebraMap ℚ K)).mpr (show p.val-1 ≠ 0 by linarith [p.property])
  · simpa only [map_add,map_one] using (map_ne_zero (algebraMap ℚ K)).mpr (show p.val+1 ≠ 0 by linarith [p.property])
  · exact (map_ne_zero (algebraMap ℚ K)).mpr (show q.val ≠ 0 by linarith [q.property])
  · simpa only [map_sub,map_one] using (map_ne_zero (algebraMap ℚ K)).mpr (show q.val-1 ≠ 0 by linarith [q.property])
  · simpa only [map_add,map_one] using (map_ne_zero (algebraMap ℚ K)).mpr (show q.val+1 ≠ 0 by linarith [q.property])

/-- An unmarked geometric isomorphism class of the ACTUAL base-changed
smooth proper models contains only finitely many parameters. -/
theorem finite_geometric_iso_fibre (q : Parameter) : {p : Parameter | geometricSetoid.r p q}.Finite := by
  have hf := HasseRationalBranchFiniteness.finite_positive_rational_fibre (K := K) q.val
  apply (hf.preimage Subtype.val_injective.injOn).subset
  intro p hp
  exact ⟨p.property,branch_equivalent_of_geometric_iso hp⟩

def familyParameter (j : ℕ) : Parameter := ⟨HpInfiniteArithmetic.p j,HpInfiniteArithmetic.p_gt_one j⟩

theorem familyParameter_injective : Function.Injective familyParameter := by
  intro i j h
  exact HpInfiniteArithmetic.parameters_injective (congrArg Subtype.val h)

/-- The displayed Hasse family contains infinitely many unmarked geometric
isomorphism classes of its actual Qbar base-changed curve models. -/
theorem infinitely_many_geometric_classes :
    Set.Infinite (Set.range (fun j : ℕ => Quotient.mk geometricSetoid (familyParameter j))) := by
  by_contra hn
  have hf := Set.not_infinite.mp hn
  have hh : (Set.univ : Set ℕ).Finite := by
    apply Set.Finite.of_finite_fibers (fun j : ℕ => Quotient.mk geometricSetoid (familyParameter j))
    · simpa using hf
    · intro c hc
      obtain ⟨j,_,rfl⟩ := hc
      have hpre := (finite_geometric_iso_fibre (familyParameter j)).preimage familyParameter_injective.injOn
      apply hpre.subset
      intro k hk
      exact Quotient.exact hk.2
  exact Set.infinite_univ hh

#print axioms literalFieldEquiv
#print axioms branch_equivalent_of_geometric_iso
#print axioms finite_geometric_iso_fibre
#print axioms infinitely_many_geometric_classes
end
end FourCorner.HpGeometricIsoFibres
