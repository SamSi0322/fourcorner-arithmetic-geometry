import ThetaCoverClassPortable.DRationalModel
import Mathlib.AlgebraicGeometry.Morphisms.Affine

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
namespace FourCorner.DCurveAffineNeighborhoods
open DRationalInputs
local instance : IsIntegral curve := integral
local instance : IsProper toBase := proper
local instance : SmoothOfRelativeDimension 1 toBase := smooth
local instance : Algebra ℚ field := constants

/-- Actual affine neighbourhood of EVERY finite set of original D/Q scheme
points, including generic/nonrational points, from its genuine constructed model. -/
theorem original_curve (F : Finset curve) :
    ∃ U : curve.Opens,IsAffineOpen U ∧ ∀x∈F,x∈U := by
  classical
  obtain ⟨M,i,hi,hg⟩ := exists_native_model
  obtain ⟨V,hV,hF⟩ := M.finset_subset_affineOpen (F.image i.hom)
  refine ⟨i.hom ⁻¹ᵁ V,hV.preimage i.hom,?_⟩
  intro x hx
  exact hF _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)

/-- Honest supporting lemma: affine pullback of affine neighbourhoods. -/
theorem along_affine {X Y : Scheme} (p : X ⟶ Y) [IsAffineHom p]
    (hY : ∀ F : Finset Y,∃ U : Y.Opens,IsAffineOpen U ∧ ∀x∈F,x∈U)
    (F : Finset X) : ∃ U : X.Opens,IsAffineOpen U ∧ ∀x∈F,x∈U := by
  classical
  obtain ⟨V,hV,hF⟩ := hY (F.image p)
  refine ⟨p ⁻¹ᵁ V,hV.preimage p,?_⟩
  intro x hx
  exact hF _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)

/-- The actual original curve after ANY affine scheme base change over Q.
This is curve AF, never AF of a represented Picard space. -/
theorem affine_basechange {B : Scheme} [IsAffine B] (y : B ⟶ Spec (.of ℚ))
    (F : Finset (pullback (C:=Scheme) (toBase) y)) :
    ∃ U : (pullback (C:=Scheme) (toBase) y).Opens,IsAffineOpen U ∧ ∀x∈F,x∈U := by
  letI : IsAffineHom y := inferInstance
  letI : IsAffineHom (pullback.fst (C:=Scheme) (toBase) y) :=
    MorphismProperty.pullback_fst (toBase) y (inferInstance : IsAffineHom y)
  exact along_affine (pullback.fst (C:=Scheme) (toBase) y) original_curve F

/-- The EXACT relative affine-neighbourhood input used to represent relative
finite divisors: every finite set lying over an affine base open lies in one
affine curve open INSIDE that preimage. The curve is the actual D/Q basechange. -/
theorem relative_affine_basechange {B : Scheme} (y : B ⟶ Spec (.of ℚ))
    (V : B.Opens) (hV : IsAffineOpen V)
    (F : Finset (pullback (C:=Scheme) (toBase) y))
    (hF : ∀x∈F,pullback.snd (C:=Scheme) (toBase) y x∈V) :
    ∃ U : (pullback (C:=Scheme) (toBase) y).Opens,
      IsAffineOpen U ∧ U≤pullback.snd (C:=Scheme) (toBase) y ⁻¹ᵁ V ∧ ∀x∈F,x∈U := by
  classical
  let cB := pullback.snd (C:=Scheme) (toBase) y
  let pB := pullback.fst (C:=Scheme) (toBase) y
  let W : (pullback (C:=Scheme) (toBase) y).Opens := cB ⁻¹ᵁ V
  let Z : Scheme := W
  let j : Z ⟶ pullback (C:=Scheme) (toBase) y := W.ι
  letI : IsAffine V.toScheme := hV
  haveI : IsAffineHom (V.ι ≫ y) := inferInstance
  have hcart : IsPullback (cB ∣_ V) (j ≫ pB) (V.ι ≫ y) (toBase) :=
    (isPullback_morphismRestrict cB V).paste_vert (IsPullback.of_hasPullback (toBase) y).flip
  letI : IsAffineHom (j ≫ pB) := MorphismProperty.of_isPullback hcart inferInstance
  let FZ : Finset Z := F.attach.image (fun x => ⟨x.val,hF x.val x.property⟩)
  obtain ⟨A,hA,hFA⟩ := along_affine (j ≫ pB) original_curve FZ
  refine ⟨j ''ᵁ A,hA.image_of_isOpenImmersion j,?_,?_⟩
  · intro x hx
    change x∈j '' (A:Set Z) at hx
    obtain ⟨z,hz,rfl⟩ := hx
    exact z.property
  · intro x hx
    let z : Z := ⟨x,hF x hx⟩
    have hz : z∈FZ := Finset.mem_image.mpr ⟨⟨x,hx⟩,Finset.mem_attach _ _,rfl⟩
    change x∈j '' (A:Set Z)
    exact ⟨z,hFA z hz,rfl⟩

#print axioms original_curve
#print axioms affine_basechange
#print axioms relative_affine_basechange
end FourCorner.DCurveAffineNeighborhoods
