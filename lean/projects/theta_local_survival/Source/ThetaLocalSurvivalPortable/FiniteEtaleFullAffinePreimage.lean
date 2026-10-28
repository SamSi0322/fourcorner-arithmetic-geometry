import ThetaLocalSurvivalPortable.FiniteEtaleAffineSchemeCovering

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FourCorner.ThetaLocalSurvival.StrongTopology
open Multiplication Infinitesimal

variable (K : Type) [Field K] [Algebra ℚ K]
  {X Y : Over base} (f : X ⟶ Y) [IsFinite f.left] [Etale f.left]
  (A : CommAlgCat ℚ) (jA : pointObject A ⟶ Y) [IsOpenImmersion jA.left]

/-- The full inverse image of an actual affine open under a finite etale scheme map
is an actual affine open; its K-point range is the FULL analytic inverse image. -/
theorem finite_etale_full_affine_preimage :
    ∃ (B : CommAlgCat ℚ) (jB : pointObject B ⟶ X) (q : pointObject B ⟶ pointObject A),
      IsOpenImmersion jB.left ∧ IsFinite q.left ∧ Etale q.left ∧ q≫jA=jB≫f ∧
      Set.range (fun R : KPoints K (pointObject B) => R≫jB) =
        (fun P : KPoints K X => P≫f) ⁻¹'
          Set.range (fun Q : KPoints K (pointObject A) => Q≫jA) := by
  letI : IsAffine (pointObject A).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  let Z := pullback f.left jA.left
  letI : IsAffine Z := inferInstanceAs (IsAffine (pullback f.left jA.left))
  let B : CommRingCat := Γ(Z,⊤)
  let u : Spec B ⟶ Z := Z.isoSpec.inv
  letI : IsIso u := inferInstanceAs (IsIso Z.isoSpec.inv)
  let rmap : ℚ →+* B := (Spec.preimage (u≫pullback.snd f.left jA.left≫(pointObject A).hom)).hom
  letI : Algebra ℚ B := rmap.toAlgebra
  have hb : u≫pullback.snd f.left jA.left≫(pointObject A).hom=(pointObject B).hom :=
    (Spec.map_preimage (u≫pullback.snd f.left jA.left≫(pointObject A).hom)).symm
  let jB : pointObject B ⟶ X := Over.homMk (u≫pullback.fst f.left jA.left) (by
    rw [←hb]
    simp only [Category.assoc]
    rw [←jA.w,←pullback.condition_assoc,f.w])
  let q : pointObject B ⟶ pointObject A := Over.homMk (u≫pullback.snd f.left jA.left)
    (by simpa only [Category.assoc] using hb)
  have hcomm : q≫jA=jB≫f := by
    apply Over.OverMorphism.ext
    change (u≫pullback.snd f.left jA.left)≫jA.left=(u≫pullback.fst f.left jA.left)≫f.left
    rw [Category.assoc,Category.assoc,pullback.condition]
  have hjB : IsOpenImmersion jB.left := by change IsOpenImmersion (u≫pullback.fst f.left jA.left); infer_instance
  have hqf : IsFinite q.left := by change IsFinite (u≫pullback.snd f.left jA.left); infer_instance
  have hqe : Etale q.left := by change Etale (u≫pullback.snd f.left jA.left); infer_instance
  refine ⟨CommAlgCat.of ℚ B,jB,q,hjB,hqf,hqe,hcomm,?_⟩
  ext P
  constructor
  · rintro ⟨R,rfl⟩
    refine ⟨R≫q,?_⟩
    change (R≫q)≫jA=(R≫jB)≫f
    rw [Category.assoc,hcomm,←Category.assoc]
  · rintro ⟨Q,hQ⟩
    have he : P.left≫f.left=Q.left≫jA.left :=
      congrArg (fun R : pointObject K ⟶ Y => R.left) hQ.symm
    let L := pullback.lift P.left Q.left he
    let R : KPoints K (pointObject B) := Over.homMk (L≫Z.isoSpec.hom) (by
      rw [←hb]
      change (L≫Z.isoSpec.hom)≫(Z.isoSpec.inv≫pullback.snd f.left jA.left≫(pointObject A).hom)=_
      dsimp only [L]
      simp only [Category.assoc,Iso.hom_inv_id_assoc,pullback.lift_snd_assoc]
      exact Q.w)
    refine ⟨R,?_⟩
    apply Over.OverMorphism.ext
    change (L≫Z.isoSpec.hom)≫(Z.isoSpec.inv≫pullback.fst f.left jA.left)=P.left
    dsimp only [L]
    simp only [Category.assoc,Iso.hom_inv_id_assoc,pullback.lift_fst]

end FourCorner.ThetaLocalSurvival.StrongTopology
