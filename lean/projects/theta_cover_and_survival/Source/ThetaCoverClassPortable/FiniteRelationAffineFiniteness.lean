import ThetaCoverClassPortable.FiniteRelationBaseFiniteness
import ThetaCoverClassPortable.FiniteRelationAffineInputs

namespace FourCorner.FiniteRelationAffineFiniteness
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FourCorner.FiniteRelationQuotient FourCorner.FiniteRelationAffineInputs
noncomputable section
universe u

/-- Actual geometric specialization of the original affine quotient
inputs. A common finite-type affine base gives a FINITE invariant
inclusion; no quotient flatness or effectiveness is assumed or asserted. -/
theorem finite_invariant_globalSections {S X R : Scheme.{u}} [IsAffine S] [IsAffine X]
    (g : X ⟶ S) [LocallyOfFiniteType g] (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    (hst : s ≫ g=t ≫ g)
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R),a ≫ s=b ≫ s→a ≫ t=b ≫ t→a=b)
    (hequiv : ∀T : Scheme.{u},Equivalence fun x y : T ⟶ X=>∃φ : T ⟶ R,φ ≫ s=x ∧ φ ≫ t=y) :
    Module.Finite (s.appTop.hom.eqLocus t.appTop.hom) Γ(X,⊤) := by
  letI : IsAffine R := isAffine_of_isAffineHom s
  letI := g.appTop.hom.toAlgebra
  have hft : Algebra.FiniteType Γ(S,⊤) Γ(X,⊤) :=
    HasRingHomProperty.appTop (P:=@LocallyOfFiniteType) g inferInstance
  letI := hft
  obtain ⟨hs,hp⟩ := finite_projective_appTop s
  have hgen := range_sup_range_eq_top s t hmono
  have heq := equivalence_ringPoints s t hequiv
  have hinj : Function.Injective (algebraMap (s.appTop.hom.eqLocus t.appTop.hom) Γ(X,⊤)) := Subtype.val_injective
  have hinv : ∀a,s.appTop.hom a=t.appTop.hom a ↔
      a∈Set.range (algebraMap (s.appTop.hom.eqLocus t.appTop.hom) Γ(X,⊤)) := by
    intro a
    constructor
    · intro h;exact ⟨⟨a,h⟩,rfl⟩
    · rintro ⟨c,rfl⟩;exact c.property
  have hbase : s.appTop.hom.comp (algebraMap Γ(S,⊤) Γ(X,⊤))=
      t.appTop.hom.comp (algebraMap Γ(S,⊤) Γ(X,⊤)) := by
    change s.appTop.hom.comp g.appTop.hom=t.appTop.hom.comp g.appTop.hom
    simpa only [Scheme.Hom.comp_appTop,CommRingCat.hom_comp] using
      congrArg (fun f : R ⟶ S=>f.appTop.hom) hst
  exact finite_of_common_finiteType_base s.appTop.hom t.appTop.hom hs hp hgen heq hinj hinv hbase

#print axioms finite_invariant_globalSections
end
end FourCorner.FiniteRelationAffineFiniteness
