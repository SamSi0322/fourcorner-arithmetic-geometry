import CriticalEllipticEvaluation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 40000
namespace FourCorner.CriticalEllipticBaseChange
abbrev nativeAlgebra (K : Type*) [Field K] : Algebra K (CriticalEllipticField.field K) := inferInstance
abbrev nativeModule (K : Type*) [Field K] : Module K (CriticalEllipticField.field K) := (nativeAlgebra K).toModule

variable (k L : Type*) [Field k] [Field L] [Algebra k L]
local instance constants : Algebra k (CriticalEllipticField.field L) :=
  ((algebraMap L (CriticalEllipticField.field L)).comp (algebraMap k L)).toAlgebra
local instance constantsModule : Module k (CriticalEllipticField.field L) := (constants k L).toModule
local instance sourceConstants : Algebra k (CriticalEllipticField.field k) := nativeAlgebra k
local instance sourceModule : Module k (CriticalEllipticField.field k) := nativeModule k
local instance nativeTargetConstants : Algebra L (CriticalEllipticField.field L) := nativeAlgebra L
local instance nativeTargetModule : Module L (CriticalEllipticField.field L) := nativeModule L
local instance targetSMul : SMul k (CriticalEllipticField.field L) := (constants k L).toSMul
local instance sourceSMul : SMul k (CriticalEllipticField.field k) := (nativeAlgebra k).toSMul
local instance nativeTargetSMul : SMul L (CriticalEllipticField.field L) := (nativeAlgebra L).toSMul
local instance tower : IsScalarTower k L (CriticalEllipticField.field L) :=
  IsScalarTower.of_algebraMap_eq (R:=k) (S:=L) (A:=CriticalEllipticField.field L) fun _=>rfl

/-- The actual native function field embeds after an extension of constants,
retaining both original x,y coordinate functions. -/
def map : CriticalEllipticField.field k →ₐ[k] CriticalEllipticField.field L := by
  have ht : Transcendental k (CriticalEllipticField.x L) := by
    intro h
    exact CriticalEllipticField.x_transcendental L (h.extendScalars (algebraMap k L).injective)
  exact CriticalEllipticEvaluation.embedding k (CriticalEllipticField.x L) (CriticalEllipticField.y L)
    (CriticalEllipticField.equation L) ht

@[simp] theorem map_x : map k L (CriticalEllipticField.x k)=CriticalEllipticField.x L := by
  unfold map
  exact CriticalEllipticEvaluation.embedding_x k _ _ _ _
@[simp] theorem map_y : map k L (CriticalEllipticField.y k)=CriticalEllipticField.y L := by
  unfold map
  exact CriticalEllipticEvaluation.embedding_y k _ _ _ _

end FourCorner.CriticalEllipticBaseChange
#print axioms FourCorner.CriticalEllipticBaseChange.map
#print axioms FourCorner.CriticalEllipticBaseChange.map_x
#print axioms FourCorner.CriticalEllipticBaseChange.map_y
