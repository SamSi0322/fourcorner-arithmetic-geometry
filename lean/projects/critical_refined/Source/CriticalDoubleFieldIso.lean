import CriticalDoubleProductBridge
import CriticalDoubleNonsquare
import CriticalCMGeneration
import CriticalQuadraticLift

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 40000
namespace FourCorner.CriticalDoubleFieldIso
open CriticalDoubleProductBridge
variable (k : Type*) [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants k i).toModule
local instance sourceConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance sourceModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (sourceConstants k i).toModule
local instance sourceRelative (i:k) : Algebra (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance sourceRelativeModule (i:k) : Module (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := (sourceRelative k i).toModule
local instance sourceTower (i:k) : IsScalarTower k (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.constants_base_tower k i

def lift (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    CriticalLiteralDouble.field k i →ₐ[k] CriticalEllipticField.field k := by
  letI : Algebra (CriticalLiteralDouble.base k i) (CriticalEllipticField.field k) :=
    (baseMap k i hi h2).toRingHom.toAlgebra
  letI : Module (CriticalLiteralDouble.base k i) (CriticalEllipticField.field k) :=
    (baseMap k i hi h2).toRingHom.toAlgebra.toModule
  letI : SMul (CriticalLiteralDouble.base k i) (CriticalEllipticField.field k) :=
    (baseMap k i hi h2).toRingHom.toAlgebra.toSMul
  letI : IsScalarTower k (CriticalLiteralDouble.base k i) (CriticalEllipticField.field k) := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    exact ((baseMap k i hi h2).commutes z).symm
  let f:=CriticalQuadraticLift.lift (CriticalLiteralDouble.radicand k i)
    (CriticalDoubleNonsquare.original_product_nonsquare k i hi h2)
    (rootValue k i hi h2) (rootValue_square k i hi h2)
  exact f.restrictScalars k

@[simp] theorem lift_base (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (z:CriticalLiteralDouble.base k i) :
    lift k i hi h2 (algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) z)=
      baseMap k i hi h2 z := by
  letI : Algebra (CriticalLiteralDouble.base k i) (CriticalEllipticField.field k) :=
    (baseMap k i hi h2).toRingHom.toAlgebra
  change (CriticalQuadraticLift.lift (E:=CriticalEllipticField.field k)
    (CriticalLiteralDouble.radicand k i)
    (CriticalDoubleNonsquare.original_product_nonsquare k i hi h2)
    (rootValue k i hi h2) (rootValue_square k i hi h2))
      (algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) z)=_
  exact AlgHom.commutes _ z

@[simp] theorem lift_root (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    lift k i hi h2 (CriticalLiteralDouble.root k i)=rootValue k i hi h2 := by
  letI : Algebra (CriticalLiteralDouble.base k i) (CriticalEllipticField.field k) :=
    (baseMap k i hi h2).toRingHom.toAlgebra
  change (CriticalQuadraticLift.lift (E:=CriticalEllipticField.field k)
    (CriticalLiteralDouble.radicand k i)
    (CriticalDoubleNonsquare.original_product_nonsquare k i hi h2)
    (rootValue k i hi h2) (rootValue_square k i hi h2))
      (Multiquadratic.Tower.stepRoot₁ (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.radicand k i))=_
  exact CriticalQuadraticLift.lift_root _ _ _ _

theorem lift_surjective (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    Function.Surjective (lift k i hi h2) := by
  let f:=lift k i hi h2
  let S:=f.fieldRange
  have hb (z:CriticalEllipticField.field k) : CriticalDoubleFieldMap.map k i hi h2 z∈S := by
    refine ⟨algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i)
      (CriticalOriginalFieldEquiv.equiv k i hi h2 z),?_⟩
    change lift k i hi h2
      (algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i)
        (CriticalOriginalFieldEquiv.equiv k i hi h2 z)) = _
    rw [lift_base]
    change CriticalDoubleFieldMap.map k i hi h2
      ((CriticalOriginalFieldEquiv.equiv k i hi h2).symm
        ((CriticalOriginalFieldEquiv.equiv k i hi h2) z)) = _
    rw [AlgEquiv.symm_apply_apply]
  have hr : rootValue k i hi h2∈S := ⟨CriticalLiteralDouble.root k i,lift_root k i hi h2⟩
  have hg : baseMap k i hi h2 (factor k i)∈S :=
    ⟨algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) (factor k i),
      lift_base k i hi h2 _⟩
  have hg0 : baseMap k i hi h2 (factor k i)≠0 :=
    (_root_.map_ne_zero (baseMap k i hi h2)).mpr (factor_nonzero k i hi h2)
  have hroot : CriticalDoubleCM.rootX (algebraMap k (CriticalEllipticField.field k) i)
      (CriticalEllipticField.x k) (CriticalEllipticField.y k)∈S := by
    have hd:=S.div_mem hr hg
    have he : rootValue k i hi h2 / baseMap k i hi h2 (factor k i)=
        CriticalDoubleCM.rootX (algebraMap k (CriticalEllipticField.field k) i)
          (CriticalEllipticField.x k) (CriticalEllipticField.y k) := by
      dsimp [rootValue]
      exact mul_div_cancel_right₀ _ hg0
    rwa [he] at hd
  have htop:=CriticalCMGeneration.eq_top_of_contains k i hi h2 S hb hroot
  intro z
  have hz:z∈S := by rw [htop];trivial
  exact hz

/-- The literal specified product-root field is genuinely isomorphic to the
independent accepted E field. Its original base map and adjoined root are
retained by lift_base and lift_root; this is not an assumed isogeny count. -/
def equiv (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    CriticalLiteralDouble.field k i ≃ₐ[k] CriticalEllipticField.field k :=
  AlgEquiv.ofBijective (lift k i hi h2) ⟨(lift k i hi h2).injective,lift_surjective k i hi h2⟩

end FourCorner.CriticalDoubleFieldIso
#print axioms FourCorner.CriticalDoubleFieldIso.lift
#print axioms FourCorner.CriticalDoubleFieldIso.lift_base
#print axioms FourCorner.CriticalDoubleFieldIso.lift_root
#print axioms FourCorner.CriticalDoubleFieldIso.lift_surjective
#print axioms FourCorner.CriticalDoubleFieldIso.equiv
