import ThetaCoverClassPortable.KummerTrivialLine
import ThetaCoverClassPortable.SmoothProperClosedPointPlaces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory TopologicalSpace
namespace FourCorner.KummerWeilLocal
open SmoothProperClosedPointPlaces
variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
    (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]

/-- A true regular unit has order zero at every actual closed point in
its domain, by the native DVR stalk/valuation-ring equivalence. -/
lemma regular_unit_order (U : X.Opens) [Nonempty U] (x : closedPoints X)
    (hx : x.val∈U) (u : Γ(X,U)ˣ) :
    letI := fieldAlgebra c
    (placeOfClosedPoint c x).ord (algebraMap Γ(X,U) X.functionField (u:Γ(X,U)))=0 := by
  letI := fieldAlgebra c
  let w := placeOfClosedPoint c x
  let a : w.toValuationSubringˣ := Units.map (stalkValuationEquiv c x).toMonoidHom
    (Units.map (X.presheaf.germ U x.val hx).hom.toMonoidHom u)
  have he : ((a:w.toValuationSubring):X.functionField)=algebraMap Γ(X,U) X.functionField (u:Γ(X,U)) := by
    change ((stalkValuationEquiv c x (X.presheaf.germ U x.val hx (u:Γ(X,U)))):X.functionField)=_
    rw [stalkValuationEquiv_coe]
    exact X.algebraMap_germ_eq_germToFunctionField hx _
  exact he ▸ w.ord_coe_unit a


section Atlas
variable {ι : Type} (U : ι → X.Opens) [∀i,Nonempty (U i)]
    (cc : Scheme.Modules.UnitCocycle U) (q : ι → X.functionField)
    (hq : ∀i,q i≠0)
    (hc : ∀i j,
      letI : Nonempty ((U i ⊓ U j : X.Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _
      algebraMap Γ(X,U i ⊓ U j) X.functionField (cc.u i j)=q j/q i)

/- True Cartier-to-Weil injectivity for these actual meromorphic frames:
a trivial sheaf yields an actual principal function, with every valuation
computed through the original closed-point DVR stalk. -/
include hq hc in
theorem isPrincipal_of_trivial [Nonempty ι]
    (hU : ⨆i,U i=⊤)
    (e : Scheme.Modules.glueOfCocycle cc ≅ SheafOfModules.unit X.ringCatSheaf)
    (Δ : letI := fieldAlgebra c; Divisor k X.functionField)
    (hΔ : letI := fieldAlgebra c
      ∀(x : closedPoints X) i,x.val∈U i →
        Δ (placeOfClosedPoint c x)= -(placeOfClosedPoint c x).ord (q i)) :
    letI := fieldAlgebra c; Δ.IsPrincipal := by
  letI := fieldAlgebra c
  obtain ⟨f,hf,hfi⟩ := KummerTrivialLine.trivial_yields_principal_data cc e q hq hc
  refine ⟨f⁻¹,inv_ne_zero hf,?_⟩
  intro v
  obtain ⟨x,rfl⟩ := placeOfClosedPoint_surjective c v
  have hx : x.val∈⨆i,U i := by rw [hU]; trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hx
  rw [hΔ x i hi,Place.ord_inv,hfi i,div_eq_mul_inv,
    (placeOfClosedPoint c x).ord_mul (hq i) (inv_ne_zero (((KummerTrivialLine.imageUnit cc e i).isUnit.map _).ne_zero)),Place.ord_inv,
    regular_unit_order c (U i) x hi (KummerTrivialLine.imageUnit cc e i)]
  omega

end Atlas

#print axioms regular_unit_order
end FourCorner.KummerWeilLocal
