import CriticalFixedPlaceEvaluation
import CriticalBoundaryClassification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open AlgebraicGeometry CategoryTheory AlgebraicCurve
universe u
namespace FourCorner.CriticalSchemeBoundary
open CriticalHomogeneousEvaluation CriticalProj23 CriticalSignPoints CriticalElliptic23 CriticalRadicalField ResiduePlaceEvaluation
open CriticalFixedPlaceEvaluation CriticalSchemePointPlaces CriticalBoundaryResidues CriticalBoundaryEight
variable {k:Type u} [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule

/-- The image of every ORIGINAL signed Scheme point under the FIXED base
place map is an actual original boundary place. -/
theorem signed_place_boundary (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (e:Fin 3→Bool) :
    let v:=baseEquiv i hi h2 (signedPoint i e)
    0<v.val.ord (shift i) := by
  let v:=baseEquiv i hi h2 (signedPoint i e)
  obtain ⟨aa,bb,cc,ha,hb,hc,hea,heb,hec⟩:=signed_coordinates i hi h2 e
  let t:=aa^2-1
  have ht:(t:CriticalLiteralDouble.base k i)=shift i := by
    change (aa:CriticalLiteralDouble.base k i)^2-1=shift i
    rw [ha]
    rfl
  have he:evaluate v.val v.property t=0 := by
    dsimp only [t]
    rw [map_sub,map_pow,map_one,hea,CriticalSignPoints.sign_sq,sub_self]
  have hn:(t:CriticalLiteralDouble.base k i)≠0 := by
    rw [ht]
    exact (CriticalBadUnits.ordered_nonzero i hi h2).2.2.2
  have hp:0<v.val.ord (t:CriticalLiteralDouble.base k i) :=
    (ResidueValuationFacts.evaluate_zero_iff_ord_pos v.val v.property t hn).mp he
  rwa [ht] at hp

/-- The FIXED original Scheme-point/place map sends the original signed
point to the matching Base8 place, retaining every a,b,c sign. -/
theorem signed_point_place (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (e:Fin 3→Bool) :
    (baseEquiv i hi h2 (signedPoint i e)).val=
      ((boundaryEquiv i hi h2).symm e).val := by
  let v:=baseEquiv i hi h2 (signedPoint i e)
  let hp:=signed_place_boundary i hi h2 e
  let w:CriticalBoundaryClassification.Boundary i:=⟨v.val,v.property,hp⟩
  obtain ⟨aa,bb,cc,ha,hb,hc,hea,heb,hec⟩:=signed_coordinates i hi h2 e
  have hA:CriticalBoundaryResidues.A i hi h2 v.val hp=aa := Subtype.ext ha.symm
  have hB:CriticalBoundaryResidues.B i hi h2 v.val hp=bb := Subtype.ext hb.symm
  have hC:CriticalBoundaryResidues.C i hi h2 v.val hp=cc := Subtype.ext hc.symm
  have hval:=boundaryEquiv_evaluations i hi h2 w
  have hl:boundaryEquiv i hi h2 w=e := by
    funext j
    apply sign_injective h2
    fin_cases j
    · exact hval.1.symm.trans (by rw [hA];exact hea)
    · exact hval.2.1.symm.trans (by rw [hB];exact heb)
    · exact hval.2.2.symm.trans (by rw [hC];exact hec)
  have hw:(boundaryEquiv i hi h2).symm e=w := by rw [←hl,Equiv.symm_apply_apply]
  exact congrArg Subtype.val hw.symm

/-- Exhaustive ORIGINAL Scheme boundary classification on all K-points,
written in the same bundled over-k point type as the fixed baseEquiv. -/
theorem boundary_iff_signed (i:k) (p:BasePoints i) :
    p.val ⁻¹ᵁ shiftOpen i=⊥ ↔ ∃e:Fin 3→Bool,p=signedPoint i e := by
  have h:=CriticalBoundaryClassification.geometric_boundary (L:=k) i p.val
    (by simpa only [Algebra.algebraMap_self,CommRingCat.ofHom_id,Spec.map_id] using p.property)
  constructor
  · intro hp
    obtain ⟨e,he⟩:=h.mp hp
    refine ⟨e,Subtype.ext ?_⟩
    change p.val=point i e
    simpa only [Algebra.algebraMap_self,CommRingCat.ofHom_id,Spec.map_id,Category.id_comp] using he
  · rintro ⟨e,rfl⟩
    exact CriticalBoundaryClassification.point_boundary i e

/-- The literal original b=V1²-V0² Scheme boundary is equivalent to positive
order of the SAME function a²-1 under the FIXED original base-place map.
This is pointwise for EVERY original K-point, not merely its signed range. -/
theorem boundary_iff_place (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (p:BasePoints i) :
    p.val ⁻¹ᵁ shiftOpen i=⊥ ↔ 0<(baseEquiv i hi h2 p).val.ord (shift i) := by
  constructor
  · intro hp
    obtain ⟨e,rfl⟩:=(boundary_iff_signed i p).mp hp
    exact signed_place_boundary i hi h2 e
  · intro hp
    let v:=baseEquiv i hi h2 p
    let w:CriticalBoundaryClassification.Boundary i:=⟨v.val,v.property,hp⟩
    let e:=boundaryEquiv i hi h2 w
    have hw:(boundaryEquiv i hi h2).symm e=w := Equiv.symm_apply_apply _ _
    have he:p=signedPoint i e := by
      apply (baseEquiv i hi h2).injective
      apply Subtype.ext
      calc
        _=w.val := rfl
        _=((boundaryEquiv i hi h2).symm e).val := (congrArg Subtype.val hw).symm
        _=_ := (signed_point_place i hi h2 e).symm
    rw [he]
    exact CriticalBoundaryClassification.point_boundary i e

abbrev BoundaryPoints (i:k) := {p:BasePoints i //p.val ⁻¹ᵁ shiftOpen i=⊥}

/-- Restrict the FIXED global point/place equivalence to the ENTIRE original
Scheme boundary. No arbitrary boundary bijection replaces that map. -/
def boundaryPointPlaceEquiv (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
    BoundaryPoints i ≃ CriticalBoundaryClassification.Boundary i where
  toFun p:=⟨(baseEquiv i hi h2 p.val).val,(baseEquiv i hi h2 p.val).property,
    (boundary_iff_place i hi h2 p.val).mp p.property⟩
  invFun v:=⟨(baseEquiv i hi h2).symm ⟨v.val,v.property.1⟩,by
    apply (boundary_iff_place i hi h2 _).mpr
    have he:=(baseEquiv i hi h2).apply_symm_apply ⟨v.val,v.property.1⟩
    rw [he]
    exact v.property.2⟩
  left_inv p:=by
    apply Subtype.ext
    exact (baseEquiv i hi h2).symm_apply_apply p.val
  right_inv v:=by
    apply Subtype.ext
    change ((baseEquiv i hi h2) ((baseEquiv i hi h2).symm ⟨v.val,v.property.1⟩)).val=v.val
    exact congrArg Subtype.val ((baseEquiv i hi h2).apply_symm_apply ⟨v.val,v.property.1⟩)

theorem boundary_card (i:k) (hi:i^2= -1) (h2:(2:k)≠0) : Nat.card (BoundaryPoints i)=8 := by
  rw [Nat.card_congr (boundaryPointPlaceEquiv i hi h2)]
  exact CriticalBoundaryEight.boundary_card i hi h2

#print axioms signed_point_place
#print axioms boundary_iff_place
#print axioms boundaryPointPlaceEquiv
#print axioms boundary_card
end FourCorner.CriticalSchemeBoundary
