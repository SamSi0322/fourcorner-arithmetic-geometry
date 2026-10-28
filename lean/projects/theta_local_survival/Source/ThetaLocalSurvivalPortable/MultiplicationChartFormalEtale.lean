import ThetaLocalSurvivalPortable.SquareZeroOpenLifting

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj FourCorner.ThetaLocalSurvival.SquareZeroScalars
namespace FourCorner.ThetaLocalSurvival.Infinitesimal
open Multiplication
variable (G : Over base) [GrpObj G]
variable (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
variable (jA : pointObject A ⟶ G) (jB : pointObject B ⟶ G)
variable (m : ℕ) (p : B →ₐ[ℚ] A)
variable (hp : pointChange p ≫ jB=jA ≫ multiplicationOver G m)

include hp in
theorem chart_point_power {R : Type} [CommRing R] [Algebra ℚ R]
    (φ : A →ₐ[ℚ] R) (β : B →ₐ[ℚ] R) (hc : φ.comp p=β) :
    (pointChange φ ≫ jA)^m=pointChange β ≫ jB := by
  rw [←multiplication_points G (pointObject R) (pointChange φ ≫ jA) m,
    Category.assoc,←hp,←Category.assoc,pointChange_comp,hc]

variable [IsCommMonObj G] [Smooth G.hom] [IsOpenImmersion jA.left] [IsOpenImmersion jB.left]

include hp in
/-- Native formal etaleness on actual affine coordinate rings of the
actual multiplication morphism, proved using actual square-zero lifts
and the unique group-kernel correction. -/
theorem multiplication_chart_formallyEtale (hm : 0<m) :
    letI : Algebra B A := p.toRingHom.toAlgebra
    Algebra.FormallyEtale B A := by
  letI : Algebra B A := p.toRingHom.toAlgebra
  letI : IsScalarTower ℚ B A := IsScalarTower.of_algebraMap_eq' p.comp_algebraMap.symm
  letI : Algebra.Smooth ℚ A := affine_chart_smooth G A jA
  apply Algebra.FormallyEtale.iff_comp_bijective.mpr
  intro R _ _ I hI
  letI : Algebra ℚ R := ((algebraMap B R).comp (algebraMap ℚ B)).toAlgebra
  letI : IsScalarTower ℚ B R := IsScalarTower.of_algebraMap_eq' rfl
  let β : B →ₐ[ℚ] R := IsScalarTower.toAlgHom ℚ B R
  constructor
  · intro f1 f2 hf
    let φ1 : A →ₐ[ℚ] R := f1.restrictScalars ℚ
    let φ2 : A →ₐ[ℚ] R := f2.restrictScalars ℚ
    have hp1 : φ1.comp p=β := by ext b;exact f1.commutes b
    have hp2 : φ2.comp p=β := by ext b;exact f2.commutes b
    have hq : (Ideal.Quotient.mkₐ ℚ I).comp φ1=(Ideal.Quotient.mkₐ ℚ I).comp φ2 := by
      ext a
      exact AlgHom.congr_fun hf a
    have hred : idealReduction G R I (pointChange φ1 ≫ jA)=
        idealReduction G R I (pointChange φ2 ≫ jA) := by
      change pointChange (Ideal.Quotient.mkₐ ℚ I) ≫ (pointChange φ1 ≫ jA)=
        pointChange (Ideal.Quotient.mkₐ ℚ I) ≫ (pointChange φ2 ≫ jA)
      rw [←Category.assoc,←Category.assoc,pointChange_comp,pointChange_comp,hq]
    have hpow : (pointChange φ1 ≫ jA)^m=(pointChange φ2 ≫ jA)^m :=
      (chart_point_power G A B jA jB m p hp φ1 β hp1).trans
        (chart_point_power G A B jA jB m p hp φ2 β hp2).symm
    have hpoints := power_injective_on_reduction_fibre G R I hI m hm _ _ hred hpow
    have hφ : φ1=φ2 := by
      apply pointChange_injective
      apply Over.OverMorphism.ext
      apply (cancel_mono jA.left).mp
      exact congrArg (fun f : pointObject R ⟶ G => f.left) hpoints
    apply AlgHom.ext
    intro a
    exact AlgHom.congr_fun hφ a
  · intro f
    let φ0 : A →ₐ[ℚ] R⧸I := f.restrictScalars ℚ
    have hp0 : φ0.comp p=(Ideal.Quotient.mkₐ ℚ I).comp β := by ext b;exact f.commutes b
    obtain ⟨φ,hφ⟩ := Algebra.FormallySmooth.comp_surjective ℚ A I hI φ0
    let P0 : points G (R⧸I) := pointChange φ0 ≫ jA
    let H : points G R := pointChange β ≫ jB
    let L : points G R := pointChange φ ≫ jA
    have hL : idealReduction G R I L=P0 := by
      change pointChange (Ideal.Quotient.mkₐ ℚ I) ≫ (pointChange φ ≫ jA)=pointChange φ0 ≫ jA
      rw [←Category.assoc,pointChange_comp,hφ]
    have hH : idealReduction G R I H=P0^m := by
      change pointChange (Ideal.Quotient.mkₐ ℚ I) ≫ (pointChange β ≫ jB)=P0^m
      rw [←Category.assoc,pointChange_comp]
      exact (chart_point_power G A B jA jB m p hp φ0 _ hp0).symm
    obtain ⟨P,⟨hPred,hPpow⟩,_⟩ := correct_square_zero_lift G R I hI m hm P0 H L hL hH
    let q := openPointLift G R I hI A jA P (pointChange φ0) hPred
    let ψ := pointToAlgHom A R q
    have hψP : pointChange ψ ≫ jA=P := by
      rw [pointChange_pointToAlgHom]
      exact openPointLift_comp G R I hI A jA P (pointChange φ0) hPred
    have hψ : (Ideal.Quotient.mkₐ ℚ I).comp ψ=φ0 := by
      apply pointChange_injective
      rw [←pointChange_comp,pointChange_pointToAlgHom]
      exact openPointLift_reduction G R I hI A jA P (pointChange φ0) hPred
    have hψp : ψ.comp p=β := by
      apply pointChange_injective
      apply Over.OverMorphism.ext
      apply (cancel_mono jB.left).mp
      have hh := chart_point_power G A B jA jB m p hp ψ (ψ.comp p) rfl
      rw [hψP,hPpow] at hh
      exact congrArg (fun f : pointObject R ⟶ G => f.left) hh.symm
    let ψB : A →ₐ[B] R :=
      { ψ.toRingHom with commutes' := fun b => AlgHom.congr_fun hψp b }
    refine ⟨ψB,?_⟩
    apply AlgHom.ext
    intro a
    exact AlgHom.congr_fun hψ a

end FourCorner.ThetaLocalSurvival.Infinitesimal
