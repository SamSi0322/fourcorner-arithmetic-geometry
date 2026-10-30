import ThetaCoverClassPortable.ThetaSinglePoleModel
import ThetaCoverClassPortable.geometry.SchemeModelTwoAffineCover

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicCurve IntermediateField
open CurveModel
namespace FourCorner.NativeSinglePoleCharts
universe u
variable {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L]
  (t : L) [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]
  [FiniteDimensional K⟮t⁻¹⟯ L] {X : Scheme.{u}}
  (i : X ≅ CurveModel.glued K t)

def jZero : CurveModel.X₀ K t ⟶ X := CurveModel.ι₀ K t ≫ i.inv
def jInfinity : CurveModel.XInf K t ⟶ X := CurveModel.ιInf K t ≫ i.inv
instance : IsOpenImmersion (jZero t i) := inferInstanceAs (IsOpenImmersion (CurveModel.ι₀ K t ≫ i.inv))
instance : IsOpenImmersion (jInfinity t i) := inferInstanceAs (IsOpenImmersion (CurveModel.ιInf K t ≫ i.inv))

def U : X.Opens := jZero t i ''ᵁ ⊤
def V : X.Opens := jInfinity t i ''ᵁ ⊤
theorem affine_U : IsAffineOpen (U t i) := (isAffineOpen_top _).image_of_isOpenImmersion (jZero t i)
theorem affine_V : IsAffineOpen (V t i) := (isAffineOpen_top _).image_of_isOpenImmersion (jInfinity t i)

def zeroSectionsEquiv : Γ(X, U t i) ≃+* chartRing K ({t} : Set L) :=
  ((jZero t i).appIso ⊤ ≪≫ Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv
def infinitySectionsEquiv : Γ(X, V t i) ≃+* chartRing K ({t⁻¹} : Set L) :=
  ((jInfinity t i).appIso ⊤ ≪≫ Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv

def fSection : Γ(X, U t i) := (zeroSectionsEquiv t i).symm (CurveModel.tChart K t)
def gSection : Γ(X, V t i) := (infinitySectionsEquiv t i).symm (CurveModel.tInvChart K t)

@[simp] theorem zeroSectionsEquiv_fSection :
    zeroSectionsEquiv t i (fSection t i) = CurveModel.tChart K t :=
  (zeroSectionsEquiv t i).apply_symm_apply _
@[simp] theorem infinitySectionsEquiv_gSection :
    infinitySectionsEquiv t i (gSection t i) = CurveModel.tInvChart K t :=
  (infinitySectionsEquiv t i).apply_symm_apply _

theorem cover : U t i ⊔ V t i = ⊤ := by
  ext x
  change (x ∈ U t i ∨ x ∈ V t i) ↔ True
  apply iff_true_intro
  obtain ⟨p,hp⟩ | ⟨p,hp⟩ := CurveModel.mem_range_ι₀_or_mem_range_ιInf K t (i.hom x)
  · left
    refine ⟨p,trivial,?_⟩
    change i.inv (CurveModel.ι₀ K t p)=x
    rw [hp]
    exact congrArg (fun g : X ⟶ X => g x) i.hom_inv_id
  · right
    refine ⟨p,trivial,?_⟩
    change i.inv (CurveModel.ιInf K t p)=x
    rw [hp]
    exact congrArg (fun g : X ⟶ X => g x) i.hom_inv_id

variable [IsIntegral X]
theorem generic_mem_U : genericPoint X ∈ U t i :=
  ⟨genericPoint (X₀ K t),trivial,genericPoint_eq_of_isOpenImmersion (jZero t i)⟩
theorem generic_mem_V : genericPoint X ∈ V t i :=
  ⟨genericPoint (XInf K t),trivial,genericPoint_eq_of_isOpenImmersion (jInfinity t i)⟩
instance nonempty_U : Nonempty (U t i) := ⟨⟨genericPoint X,generic_mem_U t i⟩⟩
instance nonempty_V : Nonempty (V t i) := ⟨⟨genericPoint X,generic_mem_V t i⟩⟩

end FourCorner.NativeSinglePoleCharts
