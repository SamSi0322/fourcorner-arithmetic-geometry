import ThetaCoverClassPortable.ThetaQuadraticRationalUnitOpens
import ThetaCoverClassPortable.ThetaQuadraticPlacePullback

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace FourCorner.ThetaQuadraticUnitCover
open ThetaQuadraticCurve ThetaQuadraticField SmoothProperClosedPointPlaces
abbrev Index := ThetaQuadraticRationalUnitOpens.NonemptyIndex
abbrev rationalOpen (i : Index) := ThetaQuadraticRationalUnitOpens.W i
def U (i : Index) : curve.Opens := toRational ⁻¹ᵁ rationalOpen i
local instance : IsIntegral curve := curve_integral
local instance : IsIntegral (ThetaLiteralModels.D ℚ) := ThetaDPlaneChartSections.original_integral
local instance : IsProper toBase := curve_proper
local instance : SmoothOfRelativeDimension 1 toBase := curve_smooth
local instance : Algebra F functionField := ThetaQuadraticCurve.fieldAlgebra
local instance : Surjective toRational := toRational_surjective
local instance (i : Index) : Nonempty (rationalOpen i) := i.property

theorem U_nonempty (i : Index) : Nonempty (U i) := by
  obtain ⟨p⟩ := (inferInstance : Nonempty (rationalOpen i))
  obtain ⟨x,hx⟩ := toRational.surjective p.val
  exact ⟨⟨x,by simpa [U,hx] using p.property⟩⟩
local instance (i : Index) : Nonempty (U i) := U_nonempty i

theorem U_affine (i : Index) : IsAffineOpen (U i) := by
  let e := P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.pullbackAffineOpenIsoSpecTensor
    (ThetaLiteralModels.dToBase ℚ) F (rationalOpen i)
      (ThetaQuadraticRationalUnitOpens.affine_U i.val)
  exact IsAffine.of_isIso e.hom

theorem cover : ⨆i : Index,U i=⊤ := by
  apply top_unique
  intro x _
  have h : toRational x∈⨆i : Index,rationalOpen i := by
    rw [ThetaQuadraticRationalUnitOpens.nonempty_cover]
    trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp h
  exact Opens.mem_iSup.mpr ⟨i,hi⟩

def unit (i : Index) : Γ(curve,U i)ˣ :=
  Units.map (toRational.app (rationalOpen i)).hom.toMonoidHom
    (ThetaQuadraticRationalUnitOpens.localUnit i.val)
def root (i : Index) : functionField :=
  fromRational (ThetaQuadraticRationalUnitOpens.root i.val)

/-- Actual regular unit on the actual pulled-back affine open, with its
exact native function-field square identity. -/
theorem unit_square (i : Index) :
    algebraMap Γ(curve,U i) functionField (unit i:Γ(curve,U i))=(root i)^2*h2 := by
  letI : Nonempty (toRational ⁻¹ᵁ rationalOpen i) := U_nonempty i
  change curve.germToFunctionField (U i)
    ((toRational.app (rationalOpen i)).hom
      (ThetaQuadraticRationalUnitOpens.localUnit i.val:Γ(ThetaLiteralModels.D ℚ,rationalOpen i)))=_
  calc
    _ = fromRational (algebraMap Γ(ThetaLiteralModels.D ℚ,rationalOpen i)
        ThetaCoverRationalData.rationalField
        (ThetaQuadraticRationalUnitOpens.localUnit i.val:Γ(ThetaLiteralModels.D ℚ,rationalOpen i))) :=
      (ThetaDChartNaturality.generic_germ_naturality toRational (rationalOpen i) _).symm
    _ = _ := by
      rw [ThetaQuadraticRationalUnitOpens.localUnit_square,map_mul,map_pow]
      rfl

theorem root_ne_zero (i : Index) : root i≠0 := by
  have hu := ((unit i).isUnit.map (algebraMap Γ(curve,U i) functionField)).ne_zero
  intro hz
  rw [unit_square,hz,zero_pow (by decide),zero_mul] at hu
  exact hu rfl

theorem regular_unit_order (V : curve.Opens) [Nonempty V] (x : closedPoints curve)
    (hx : x.val∈V) (a : Γ(curve,V)ˣ) :
    (placeOfClosedPoint toBase x).ord (algebraMap Γ(curve,V) functionField (a:Γ(curve,V)))=0 := by
  let w := placeOfClosedPoint toBase x
  let u : w.toValuationSubringˣ := Units.map (stalkValuationEquiv toBase x).toMonoidHom
    (Units.map (curve.presheaf.germ V x.val hx).hom.toMonoidHom a)
  have he : ((u:w.toValuationSubring):functionField)=
      algebraMap Γ(curve,V) functionField (a:Γ(curve,V)) := by
    change ((stalkValuationEquiv toBase x (curve.presheaf.germ V x.val hx (a:Γ(curve,V)))):functionField)=_
    rw [stalkValuationEquiv_coe]
    exact curve.algebraMap_germ_eq_germToFunctionField hx _
  exact he ▸ w.ord_coe_unit u

/-- Evenness at EVERY native F-place is derived from the actual six-chart
unit-root covering, rather than postulated as a descent datum. -/
theorem h2_order_even (w : Place F functionField) : Even (w.ord h2) := by
  obtain ⟨x,rfl⟩ := placeOfClosedPoint_surjective toBase w
  have hx : x.val∈⨆i : Index,U i := by rw [cover];trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hx
  let v := placeOfClosedPoint toBase x
  have hu := regular_unit_order (U i) x hi (unit i)
  rw [unit_square,pow_two,v.ord_mul (mul_ne_zero (root_ne_zero i) (root_ne_zero i)) h2_ne_zero,
    v.ord_mul (root_ne_zero i) (root_ne_zero i)] at hu
  change Even (v.ord h2)
  change v.ord (root i)+v.ord (root i)+v.ord h2=0 at hu
  exact ⟨-v.ord (root i),by omega⟩

end FourCorner.ThetaQuadraticUnitCover
