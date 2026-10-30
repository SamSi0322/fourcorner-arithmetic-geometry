import ThetaCoverClassPortable.FiniteMapLaurentSections
import ThetaCoverClassPortable.LaurentLocalizedSections

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory NeronModelInfra Polynomial LaurentPolynomial
universe u
namespace FourCorner.FiniteMapCohomology
variable {R : Type u} [CommRing R]

theorem positive_X_isUnit (S : TwoChartCech.Sections (laurentCover R)) :
    letI : Module R[X] S.M01 := Module.compHom S.M01 (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R)
    IsUnit (algebraMap R[X] (Module.End R[X] S.M01) X) := by
  letI : Module R[X] S.M01 := Module.compHom S.M01 (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R)
  rw [Module.End.isUnit_iff]
  change Function.Bijective (fun z : S.M01 => Polynomial.toLaurent (X : R[X]) • z)
  rw [Polynomial.toLaurent_X]
  exact (LaurentPolynomial.isUnit_T (R := R) 1).smul_bijective

theorem negative_X_isUnit (S : TwoChartCech.Sections (laurentCover R)) :
    letI : Module R[X] S.M01 := Module.compHom S.M01
      (LaurentPolynomial.invert.toRingHom.comp (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R))
    IsUnit (algebraMap R[X] (Module.End R[X] S.M01) X) := by
  letI : Module R[X] S.M01 := Module.compHom S.M01
    (LaurentPolynomial.invert.toRingHom.comp (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R))
  rw [Module.End.isUnit_iff]
  change Function.Bijective (fun z : S.M01 => LaurentPolynomial.invert (Polynomial.toLaurent (X : R[X])) • z)
  rw [Polynomial.toLaurent_X,LaurentPolynomial.invert_T]
  exact (LaurentPolynomial.isUnit_T (R := R) (-1)).smul_bijective

variable {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}

theorem finiteMap_positive_localizes (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    PositiveLocalizes (finiteMapLaurentSections F M) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c F.U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c F.V
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c (F.U ⊓ F.V)
  unfold PositiveLocalizes
  let S := finiteMapLaurentSections F M
  letI : Module R[X] S.M01 := Module.compHom S.M01 (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R)
  refine IsLocalizedModule.Away.mk_of_addCommGroup (positive_X_isUnit S) ?_ ?_
  · intro z
    change Γ(M,F.U ⊓ F.V) at z
    obtain ⟨n,x,hx⟩ := (positive_overlap_localization F M htriv).1 z
    refine ⟨n,x,?_⟩
    change laurentEvaluation (R := R) (overlapUnit F) (Polynomial.toLaurent (X^n : R[X])) • z = restrictPositive F M x
    rw [laurentEvaluation_plus,map_pow,Polynomial.aeval_X]
    exact hx.symm
  · intro x hx
    change Γ(M,F.U) at x
    obtain ⟨n,hn⟩ := (positive_overlap_localization F M htriv).2 x hx
    refine ⟨n,?_⟩
    change (Polynomial.aeval F.f : R[X] →ₐ[R] Γ(C,F.U)) (X^n) • x = 0
    rw [map_pow,Polynomial.aeval_X]
    exact hn

theorem finiteMap_negative_localizes (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    NegativeLocalizes (finiteMapLaurentSections F M) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c F.U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c F.V
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c (F.U ⊓ F.V)
  unfold NegativeLocalizes
  let S := finiteMapLaurentSections F M
  letI : Module R[X] S.M01 := Module.compHom S.M01
    (LaurentPolynomial.invert.toRingHom.comp (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R))
  refine IsLocalizedModule.Away.mk_of_addCommGroup (negative_X_isUnit S) ?_ ?_
  · intro z
    change Γ(M,F.U ⊓ F.V) at z
    obtain ⟨n,y,hy⟩ := (negative_overlap_localization F M htriv).1 z
    refine ⟨n,y,?_⟩
    change laurentEvaluation (R := R) (overlapUnit F)
      (LaurentPolynomial.invert (Polynomial.toLaurent (X^n : R[X]))) • z = restrictNegative F M y
    rw [laurentEvaluation_minus,map_pow,Polynomial.aeval_X]
    exact hy.symm
  · intro y hy
    change Γ(M,F.V) at y
    obtain ⟨n,hn⟩ := (negative_overlap_localization F M htriv).2 y hy
    refine ⟨n,?_⟩
    change (Polynomial.aeval F.g : R[X] →ₐ[R] Γ(C,F.V)) (X^n) • y = 0
    rw [map_pow,Polynomial.aeval_X]
    exact hn
end FourCorner.FiniteMapCohomology
