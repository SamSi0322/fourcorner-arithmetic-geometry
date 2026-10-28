import ThetaLocalSurvivalPortable.MultiplicationChartFormalEtale

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj FourCorner.ThetaLocalSurvival.SquareZeroScalars
namespace FourCorner.ThetaLocalSurvival.Multiplication
open Infinitesimal
variable (G : Over base) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]

/-- Multiplication by every positive m on the ACTUAL smooth commutative
group scheme over QQ is etale. The proof uses the genuine native
square-zero lifting criterion on its actual affine section rings. -/
theorem multiplication_etale (m : ℕ) (hm : 0<m) : Etale (multiplication G m) := by
  constructor
  intro U hU V hV e
  let A : CommRingCat := Γ(G.left,V)
  let B : CommRingCat := Γ(G.left,U)
  let fA : Spec A ⟶ G.left := hV.fromSpec
  let fB : Spec B ⟶ G.left := hU.fromSpec
  let qA : ℚ →+* A := (Spec.preimage (fA ≫ G.hom)).hom
  let qB : ℚ →+* B := (Spec.preimage (fB ≫ G.hom)).hom
  letI : Algebra ℚ A := qA.toAlgebra
  letI : Algebra ℚ B := qB.toAlgebra
  have hbA : fA ≫ G.hom=(pointObject A).hom := (Spec.map_preimage (fA ≫ G.hom)).symm
  have hbB : fB ≫ G.hom=(pointObject B).hom := (Spec.map_preimage (fB ≫ G.hom)).symm
  let jA : pointObject A ⟶ G := Over.homMk fA hbA
  let jB : pointObject B ⟶ G := Over.homMk fB hbB
  letI : IsOpenImmersion jA.left := by change IsOpenImmersion hV.fromSpec;infer_instance
  letI : IsOpenImmersion jB.left := by change IsOpenImmersion hU.fromSpec;infer_instance
  let g : B →+* A := ((multiplication G m).appLE U V e).hom
  have hc : Spec.map (CommRingCat.ofHom g) ≫ fB=fA ≫ multiplication G m :=
    hU.SpecMap_appLE_fromSpec (multiplication G m) hV e
  have hk : Spec.map (CommRingCat.ofHom g) ≫ (pointObject B).hom=(pointObject A).hom := by
    rw [←hbB,←Category.assoc,hc,Category.assoc,multiplication_over,hbA]
  let k : pointObject A ⟶ pointObject B := Over.homMk (Spec.map (CommRingCat.ofHom g)) hk
  let p : B →ₐ[ℚ] A := pointToAlgHom B A k
  have hpk : pointChange p=k := pointChange_pointToAlgHom B A k
  have hpeq : p.toRingHom=g := by
    have hh := congrArg (fun f : pointObject A ⟶ pointObject B => f.left) hpk
    change Spec.map (CommRingCat.ofHom p.toRingHom)=Spec.map (CommRingCat.ofHom g) at hh
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hh)
  have hp : pointChange p ≫ jB=jA ≫ multiplicationOver G m := by
    rw [hpk]
    apply Over.OverMorphism.ext
    exact hc
  letI : Algebra B A := p.toRingHom.toAlgebra
  letI : IsScalarTower ℚ B A := IsScalarTower.of_algebraMap_eq' p.comp_algebraMap.symm
  letI : Algebra.Smooth ℚ A := affine_chart_smooth G A jA
  letI : Algebra.Smooth ℚ B := affine_chart_smooth G B jB
  letI : Algebra.FormallyEtale B A := multiplication_chart_formallyEtale G A B jA jB m p hp hm
  letI : Algebra.FinitePresentation B A := Algebra.FinitePresentation.of_restrict_scalars_finitePresentation ℚ B A
  have hEt : p.toRingHom.Etale := by
    change Algebra.Etale B A
    exact ⟨inferInstance,inferInstance⟩
  change g.Etale
  rw [←hpeq]
  exact hEt

/-- Exact finite-etale multiplication bridge used by local survival.
Properness is genuine scheme properness; no finite or etale input is
assumed for the multiplication morphism. -/
theorem multiplication_finite_etale [IsProper G.hom] (m : ℕ) (hm : 0<m) :
    IsFinite (multiplication G m) ∧ Etale (multiplication G m) :=
  (finite_etale_iff_etale G m).mpr (multiplication_etale G m hm)

theorem all_positive_multiplications_finite_etale [IsProper G.hom] :
    ∀m : ℕ,1≤m → IsFinite (multiplication G m) ∧ Etale (multiplication G m) := by
  intro m hm
  exact multiplication_finite_etale G m (lt_of_lt_of_le Nat.zero_lt_one hm)

end FourCorner.ThetaLocalSurvival.Multiplication
