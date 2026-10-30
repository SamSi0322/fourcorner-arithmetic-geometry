import HpGeometricNonisoAudit
import HpLiteralGeometric

/-! Geometric nonisomorphism for the ORIGINAL literal P4 curves, using
only the proved native base-compatible geometric isomorphism to their
canonical models. All affine/projective charts and the exact parameter
are retained in that comparison. -/
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace FourCorner.HpLiteralGeometricNoniso
open AlgebraicGeometry CategoryTheory HpGeometricIsoFibres
noncomputable section
attribute [local instance] Classical.propDecidable

def geometricObject (p : Parameter) : Over (Spec (CommRingCat.of K)) :=
  Over.mk (HpLiteralGeometric.geometricToBase p.val)

/-- The actual Qbar base change of the original literal P4 curve, compared
over the same Qbar base to the proved canonical model. -/
def objectIso (p : Parameter) : geometricObject p ≅ HpGeometricIsoFibres.geometricObject p :=
  Over.isoMk (HpLiteralGeometric.geometricIso p.val p.property)
    (HpLiteralGeometric.geometricIso_over p.val p.property)

def geometricSetoid : Setoid Parameter where
  r p q := Nonempty (geometricObject p ≅ geometricObject q)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩,fun ⟨e⟩ => ⟨e.symm⟩,fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

theorem canonical_iso_of_literal_iso {p q : Parameter} (h : geometricSetoid.r p q) :
    HpGeometricIsoFibres.geometricSetoid.r p q := by
  obtain ⟨e⟩ := h
  exact ⟨(objectIso p).symm ≪≫ e ≪≫ objectIso q⟩

/-- Finite unmarked geometric-isomorphism fibres for the exact original C_p. -/
theorem finite_geometric_iso_fibre (q : Parameter) : {p : Parameter | geometricSetoid.r p q}.Finite :=
  (HpGeometricIsoFibres.finite_geometric_iso_fibre q).subset fun _ hp => canonical_iso_of_literal_iso hp

/-- The missing geometric clause of thm:hp-infinite: the actual original
literal family has infinitely many unmarked geometric isomorphism classes. -/
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

#print axioms objectIso
#print axioms canonical_iso_of_literal_iso
#print axioms finite_geometric_iso_fibre
#print axioms infinitely_many_geometric_classes
end
end FourCorner.HpLiteralGeometricNoniso
