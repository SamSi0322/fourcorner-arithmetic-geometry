import ThetaCoverClassPortable.AllOrdersRegularUnits

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle
namespace FourCorner.CartierWeilInjectivity
open SmoothProperClosedPointPlaces
variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
    (a : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 a] [IsProper a]
    {ι : Type} (U : ι → X.Opens) [∀i,Nonempty (U i)] (hAff : ∀i,IsAffineOpen (U i))
    (c d : UnitCocycle U) (q r : ι → X.functionField)
    (hq : ∀i,q i≠0) (hr : ∀i,r i≠0)
    (hc : ∀i j,
      letI : Nonempty ((U i ⊓ U j : X.Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _
      algebraMap Γ(X,U i ⊓ U j) X.functionField (c.u i j)=q j/q i)
    (hd : ∀i j,
      letI : Nonempty ((U i ⊓ U j : X.Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _
      algebraMap Γ(X,U i ⊓ U j) X.functionField (d.u i j)=r j/r i)
    (hord : letI := fieldAlgebra a
      ∀(x : closedPoints X) i,x.val∈U i →
        (placeOfClosedPoint a x).ord (q i)=(placeOfClosedPoint a x).ord (r i))

include hAff hq hr hord in
lemma ratio_unit_exists (i : ι) : ∃g : Γ(X,U i)ˣ,
    algebraMap Γ(X,U i) X.functionField (g:Γ(X,U i))=q i/r i := by
  letI := fieldAlgebra a
  apply AllOrdersRegularUnits.unit_of_zero_orders a (U i) (hAff i) (q i/r i) (div_ne_zero (hq i) (hr i))
  intro x hx
  rw [div_eq_mul_inv,(placeOfClosedPoint a x).ord_mul (hq i) (inv_ne_zero (hr i)),
    Place.ord_inv,hord x i hx]
  omega

def ratioUnit (i : ι) : Γ(X,U i)ˣ := (ratio_unit_exists a U hAff q r hq hr hord i).choose

lemma ratioUnit_field (i : ι) :
    algebraMap Γ(X,U i) X.functionField (ratioUnit a U hAff q r hq hr hord i:Γ(X,U i))=q i/r i :=
  (ratio_unit_exists a U hAff q r hq hr hord i).choose_spec

local instance pair_nonempty (i j : ι) : Nonempty ((U i ⊓ U j : X.Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _

include hc hd in
lemma frame_coefficient_transition (i j : ι) :
    rO (inf_le_right : U i ⊓ U j ≤ U j) (ratioUnit a U hAff q r hq hr hord j:Γ(X,U j))*d.u i j=
      c.u i j*rO inf_le_left (ratioUnit a U hAff q r hq hr hord i:Γ(X,U i)) := by
  apply X.germToFunctionField_injective (U i ⊓ U j)
  change algebraMap Γ(X,U i ⊓ U j) X.functionField _ = algebraMap Γ(X,U i ⊓ U j) X.functionField _
  rw [map_mul,map_mul,KummerUnitCocycle.germ_res,KummerUnitCocycle.germ_res,
    ratioUnit_field,ratioUnit_field,hc,hd]
  field_simp [hq i,hr i,hr j]
  <;> ring

/- Equal orders of genuine local meromorphic frames give an actual
isomorphism of structure-sheaf modules. The regular coefficients of the
isomorphism are constructed from DVR intersections, not postulated. -/
include hc hd in
theorem exists_iso_of_equal_orders (hU : ⨆i,U i=⊤) :
    ∃e : glueOfCocycle c ≅ glueOfCocycle d,∀i,
      e.hom.app (U i) (glueFrame c i)=
        (ratioUnit a U hAff q r hq hr hord i:Γ(X,U i)) • glueFrame d i := by
  let f : ∀i,Γ(glueOfCocycle d,U i) := fun i=>
    (ratioUnit a U hAff q r hq hr hord i:Γ(X,U i)) • glueFrame d i
  have hf : ∀i,IsFrameOn (f i) (U i) := fun i=>
    P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_twist_iso.AlgebraicGeometry.Scheme.Modules.GlueT2.isFrameOn_unit_smul
      (isFrameOn_glueFrame d i) _ (ratioUnit a U hAff q r hq hr hord i).isUnit
  have ht : ∀i j,(glueOfCocycle d).presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (f j)=
      c.u i j • (glueOfCocycle d).presheaf.map (homOfLE inf_le_left).op (f i) := by
    intro i j
    simp only [f,Scheme.Modules.map_smul,map_glueFrame_eq_smul,smul_smul]
    rw [frame_coefficient_transition a U hAff c d q r hq hr hc hd hord i j]
  obtain ⟨e,he⟩ := exists_iso_glueOfCocycle_app_eq_glueFrame hU c f hf ht
  refine ⟨e.symm,fun i=>?_⟩
  rw [Iso.symm_hom,←he i,KummerSquareLine.iso_inv_app_hom_app]

#print axioms exists_iso_of_equal_orders
end FourCorner.CartierWeilInjectivity
