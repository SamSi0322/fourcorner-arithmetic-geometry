import HpLiteralFamilyConstituents
import HpLiteralGeometricNonisoAudit

/-! Full exact original thm:hp-infinite, including infinitely many native
unmarked geometric isomorphism classes of the ORIGINAL literal P4 curves.
This is a joint private candidate; statement credit is decided by root. -/
namespace FourCorner.HpInfiniteComplete
open AlgebraicGeometry CategoryTheory
noncomputable section

/-- All per-member paper conclusions on the original literal C_p. -/
def MemberConclusion (j : ℕ) : Prop :=
    let p := HpInfiniteArithmetic.p j
    1<p ∧ HasseNorms.Domain p ∧ HasseObstructionArithmetic.T p=1 ∧ HasseNorms.Loc p ∧
    IsClosedImmersion (HpLiteralProjective.inclusion ℚ p) ∧
    IsIntegral (HpLiteralProjective.curve ℚ p) ∧
    IsProper (HpLiteralProjective.toBase ℚ p) ∧
    SmoothOfRelativeDimension 1 (HpLiteralProjective.toBase ℚ p) ∧
    GeometricallyConnected (HpLiteralProjective.toBase ℚ p) ∧
    (let c := HpLiteralGeometric.geometricToBase p
     letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
     Module.Finite (AlgebraicClosure ℚ) Γ(c.kaehler,⊤) ∧
       Module.finrank (AlgebraicClosure ℚ) Γ(c.kaehler,⊤)=5) ∧
    (∀q : ℕ,∀[Fact q.Prime],∃f : Spec (.of ℚ_[q]) ⟶ HpLiteralProjective.curve ℚ p,
      f ≫ HpLiteralProjective.toBase ℚ p=Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ_[q]))) ∧
    (∃S : HasseNorms.LocalPoint ℝ (p : ℝ),1<S.rho ∧
      0<2*S.t^2-4*|S.u|-|S.v*S.w| ∧
      HpLiteralPoints.point (K:=ℚ) (L:=ℝ) p S ≫ HpLiteralProjective.toBase ℚ p=
        Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ))) ∧
    (¬∃f : Spec (.of ℚ) ⟶ HpLiteralProjective.curve ℚ p,f ≫ HpLiteralProjective.toBase ℚ p=𝟙 _)

/-- The full manuscript theorem: exact displayed parameters, actual
smooth proper geometrically connected genus-five literal curves with points
at every completion (including the strict real region), no rational point,
and INFINITELY MANY UNMARKED geometric isomorphism classes. -/
theorem hp_infinite :
    (Set.range HpInfiniteArithmetic.p).Infinite ∧
    (∀j : ℕ,MemberConclusion j) ∧
    Set.Infinite (Set.range (fun j : ℕ => Quotient.mk HpLiteralGeometricNoniso.geometricSetoid
      (HpGeometricIsoFibres.familyParameter j))) := by
  refine ⟨HpInfiniteArithmetic.infinitely_many_parameters,?_,?_⟩
  · intro j
    exact HpLiteralFamilyConstituents.all_members j
  · exact HpLiteralGeometricNonisoAudit.original_family_infinite_geometric_classes

#print axioms hp_infinite
#print MemberConclusion
#print HpLiteralGeometricNoniso.geometricSetoid
#print HpLiteralGeometricNoniso.geometricObject
end
end FourCorner.HpInfiniteComplete
