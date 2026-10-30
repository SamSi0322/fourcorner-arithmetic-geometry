import geometry.SchemeModelFiniteExtension

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.GenericNormalizedGluing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
universe u
variable (K L : Type u) [Field K] [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
variable {Y : Scheme.{u}}

local instance spanMapsOpen : ∀ {i j} (a : i ⟶ j),
    IsOpenImmersion ((span (CurveModel.f₀ K t) (CurveModel.fInf K t)).map a) := by
  intro i j a
  cases a with
  | id i => rw [span_map_id]; infer_instance
  | init i =>
    cases i with
    | left => rw [span_map_fst]; exact CurveModel.isOpenImmersion_f₀ K t
    | right => rw [span_map_snd]; exact CurveModel.isOpenImmersion_fInf K t

def desc (f : CurveModel.X₀ K t ⟶ Y) (g : CurveModel.XInf K t ⟶ Y)
    (h : CurveModel.f₀ K t ≫ f = CurveModel.fInf K t ≫ g) : CurveModel.glued K t ⟶ Y := by
  change pushout (CurveModel.f₀ K t) (CurveModel.fInf K t) ⟶ Y
  exact pushout.desc f g h

lemma zero_desc (f : CurveModel.X₀ K t ⟶ Y) (g : CurveModel.XInf K t ⟶ Y)
    (h : CurveModel.f₀ K t ≫ f = CurveModel.fInf K t ≫ g) :
    CurveModel.ι₀ K t ≫ desc K L t f g h = f := pushout.inl_desc _ _ _
lemma infinity_desc (f : CurveModel.X₀ K t ⟶ Y) (g : CurveModel.XInf K t ⟶ Y)
    (h : CurveModel.f₀ K t ≫ f = CurveModel.fInf K t ≫ g) :
    CurveModel.ιInf K t ≫ desc K L t f g h = g := pushout.inr_desc _ _ _
lemma hom_ext (f g : CurveModel.glued K t ⟶ Y)
    (h0 : CurveModel.ι₀ K t ≫ f = CurveModel.ι₀ K t ≫ g)
    (hInf : CurveModel.ιInf K t ≫ f = CurveModel.ιInf K t ≫ g) : f=g :=
  pushout.hom_ext h0 hInf

#print axioms desc
#print axioms zero_desc
#print axioms infinity_desc
#print axioms hom_ext
end FourCorner.GenericNormalizedGluing
