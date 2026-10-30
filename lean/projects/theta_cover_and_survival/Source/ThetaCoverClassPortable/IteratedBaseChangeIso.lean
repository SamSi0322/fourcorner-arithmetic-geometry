import ThetaCoverClassPortable.StructuralGlobalSectionsIso

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IteratedStructuralBaseChange

/-- The base algebra is built explicitly through A -> R -> S. -/
@[instance_reducible]
def composedAlgebra (A R S : Type u) [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra R S] : Algebra A S :=
  ((algebraMap R S).comp (algebraMap A R)).toAlgebra

theorem composedTower (A R S : Type u) [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra R S] :
    letI := composedAlgebra A R S
    IsScalarTower A R S := by
  letI := composedAlgebra A R S
  exact IsScalarTower.of_algebraMap_eq' rfl

section Tower
variable {A R S : Type u} [CommRing A] [CommRing R] [CommRing S]
  [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S]

/-- Spec reverses the actual composite algebra map, including for zero rings. -/
theorem specMap_comp :
    Scheme.TwoAffineOpenCover.specMap R S ≫ Scheme.TwoAffineOpenCover.specMap A R =
      Scheme.TwoAffineOpenCover.specMap A S := by
  change Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A R)) =
    Spec.map (CommRingCat.ofHom (algebraMap A S))
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq A R S).symm

/-- Canonical pullback pasting followed by the PROVED Spec composite equality. -/
def baseChangeIso {X : Scheme.{u}} (c : X ⟶ Spec (.of A)) :
    pullback (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A R))
      (Scheme.TwoAffineOpenCover.specMap R S) ≅
    pullback c (Scheme.TwoAffineOpenCover.specMap A S) :=
  pullbackLeftPullbackSndIso c (Scheme.TwoAffineOpenCover.specMap A R)
      (Scheme.TwoAffineOpenCover.specMap R S) ≪≫
    pullback.congrHom rfl specMap_comp

/-- The canonical comparison is an ACTUAL over-S isomorphism. -/
theorem baseChangeIso_over {X : Scheme.{u}} (c : X ⟶ Spec (.of A)) :
    (baseChangeIso (R := R) (S := S) c).hom ≫
        pullback.snd c (Scheme.TwoAffineOpenCover.specMap A S) =
      pullback.snd (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A R))
        (Scheme.TwoAffineOpenCover.specMap R S) := by
  simp [baseChangeIso, pullback.congrHom_hom, pullback.map]

/-- The same actual comparison preserves the EXACT S-structure on global sections. -/
def sectionsAlgEquiv {X : Scheme.{u}} (c : X ⟶ Spec (.of A)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A S)) ⊤
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (pullback.snd (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A R))
        (Scheme.TwoAffineOpenCover.specMap R S)) ⊤
    Γ(pullback c (Scheme.TwoAffineOpenCover.specMap A S), ⊤) ≃ₐ[S]
      Γ(pullback (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A R))
        (Scheme.TwoAffineOpenCover.specMap R S), ⊤) :=
  Scheme.StructuralGlobalSections.sectionsAlgEquiv _ _
    (baseChangeIso c) (baseChangeIso_over c)

/-- Actual universal structural H0 passes through canonical iterated base change. -/
theorem bijective_algebraMap_iterated {X : Scheme.{u}} (c : X ⟶ Spec (.of A))
    (hS : letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A S)) ⊤
      Function.Bijective (algebraMap S
        Γ(pullback c (Scheme.TwoAffineOpenCover.specMap A S), ⊤))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (pullback.snd (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A R))
        (Scheme.TwoAffineOpenCover.specMap R S)) ⊤
    Function.Bijective (algebraMap S
      Γ(pullback (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A R))
        (Scheme.TwoAffineOpenCover.specMap R S), ⊤)) :=
  Scheme.StructuralGlobalSections.bijective_algebraMap_of_overIso _ _
    (baseChangeIso c) (baseChangeIso_over c) hS

end Tower

/-- No externally supplied A-algebra or tower on S is required: both are constructed. -/
def baseChangeIsoViaComposite {A R S : Type u} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra R S] {X : Scheme.{u}} (c : X ⟶ Spec (.of A)) :
    letI := composedAlgebra A R S
    pullback (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A R))
      (Scheme.TwoAffineOpenCover.specMap R S) ≅
    pullback c (Scheme.TwoAffineOpenCover.specMap A S) := by
  letI := composedAlgebra A R S
  letI : IsScalarTower A R S := composedTower A R S
  exact baseChangeIso c

end AlgebraicGeometry.Scheme.IteratedStructuralBaseChange
