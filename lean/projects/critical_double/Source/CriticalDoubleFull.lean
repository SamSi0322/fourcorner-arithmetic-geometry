import CriticalDoubleFullGeometry
import CriticalNormalizationDiagram
import CriticalSchemeBoundaryCount

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
open AlgebraicGeometry CategoryTheory AlgebraicCurve
universe u
namespace FourCorner.CriticalDoubleFull

/-- The full finite-field statement uses actual Scheme points and the
actual fixed cover map. Its character is represented in a native affine
chart of the SAME original point, including the V0=0 locus. -/
def PrimeStatement (p:ℕ) [Fact p.Prime] (hmod:p%4=1)
 (i:ZMod p) (hi:i^2= -1) : Prop :=
 let hp2:p≠2:=by omega
 let h2:(2:ZMod p)≠0:=Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp2)
 Nat.card (CriticalSchemeBoundaryCount.BoundaryPoints i hi h2)=(if p%8=1 then 16 else 8) ∧
 Nat.card (CriticalLiteralCount.PositivePoints i hi h2)=
 (Nat.card (CriticalSchemePointPlaces.CoverPoints (k:=ZMod p))-
 Nat.card (CriticalSchemeBoundaryCount.BoundaryPoints i hi h2))/2 ∧
 (∀P:CriticalSchemePointPlaces.BasePoints i,
 ∃(j:Fin 4) (f:CriticalStandardCharts.affineRing i j→ₐ[ZMod p]ZMod p),
 (j=0 ∨j=1) ∧CriticalChartResidueEvaluation.affinePoint i j f=P ∧
 let v:=CriticalChartSmooth.normalizedVector j (fun a=>f (CriticalChartJacobian.ax i j a))
 CriticalSchemeCount.residueVector i hi h2 P=v ∧
 CriticalSchemeCount.character i hi h2 P=quadraticChar (ZMod p) (2*(v 0*v 3+v 1*v 2))) ∧
 (∀(V:Fin 4→ZMod p) (a:ZMod p),a≠0→
 quadraticChar (ZMod p) (2*CriticalProjectiveCharacter.product (fun j=>a*V j))=
 quadraticChar (ZMod p) (2*CriticalProjectiveCharacter.product V))

theorem finite_statement (p:ℕ) [Fact p.Prime] (hmod:p%4=1)
 (i:ZMod p) (hi:i^2= -1) : PrimeStatement p hmod i hi := by
 let hp2:p≠2:=by omega
 let h2:(2:ZMod p)≠0:=Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp2)
 exact ⟨CriticalSchemeBoundaryCount.boundary_count_mod_eight hmod i hi h2,
 CriticalSchemeBoundaryCount.count i hi h2,
 CriticalLiteralSchemeCharacter.literal_character i hi h2,
 fun V a ha=>CriticalProjectiveCharacter.rescale V a ha⟩

variable {k:Type u} [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule
local instance relative (i:k) : Algebra (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance relativeModule (i:k) : Module (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := (relative i).toModule

/-- Explicit relative field and generic-Spec diagrams identify the ACTUAL
Scheme map with the literal root extension under the supplied fixed maps. -/
def NativeNormalization (i:k) (hi:i^2= -1) (h2:(2:k)≠0) : Prop :=
 letI:=CriticalAffineDomain.ring_isDomain i hi h2
 letI:=CriticalProjectiveIntegral.projective_integral i hi h2
 letI:=EllipticQuarticModel.integral k
 letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
 letI:=SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
 (CriticalDoubleOriginalMap.pullback i hi h2).toRingHom.comp
 (CriticalDoubleOriginalMap.baseFieldEquiv i hi h2).toRingHom=
 (CriticalDoubleModel.fieldEquiv i hi h2).toRingHom.comp
 (algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i)) ∧
 (EllipticQuarticModel.curve k).fromSpecStalk (genericPoint (EllipticQuarticModel.curve k)) ≫
 CriticalDoubleOriginalMap.map i hi h2=
 Spec.map (CommRingCat.ofHom (CriticalDoubleOriginalMap.pullback i hi h2).toRingHom) ≫
 (CriticalProj23.criticalCurve i).fromSpecStalk (genericPoint (CriticalProj23.criticalCurve i))

theorem native_normalization (i:k) (hi:i^2= -1) (h2:(2:k)≠0) : NativeNormalization i hi h2 :=
 ⟨CriticalNormalizationDiagram.field_diagram i hi h2,CriticalDoubleOriginalMap.map_generic i hi h2⟩

/-- Complete prop:crit-double: the ACTUAL normalized original cover is
geometrically connected, finite etale of degree two, between smooth proper
genus-one curves with rational points; actual boundary counts and the
literal same-point projective character count hold for every indicated
prime. Every chart normalization retains the same primitive extension.
There is no source-existence, point-count or geometric input premise. -/
theorem prop_crit_double (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
 (CriticalDoubleFullGeometry.Geometry i hi h2 ∧
 CriticalDoubleFullGeometry.DegreeTwo i hi h2 ∧
 CriticalDoubleFullGeometry.GeometricGenusOne i hi h2) ∧
 NativeNormalization i hi h2 ∧
 (∀q:CriticalLiteralDouble.base k i,
 (CriticalLiteralDouble.root k i / algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) q)^2=
 algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i)
   (CriticalLiteralDouble.radicand k i / q^2) ∧
 (q≠0→Algebra.adjoin (CriticalLiteralDouble.base k i)
 {CriticalLiteralDouble.root k i / algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) q}=⊤)) ∧
 (∀(p:ℕ) [Fact p.Prime] (hmod:p%4=1) (i:ZMod p) (hi:i^2= -1),PrimeStatement p hmod i hi) := by
 refine ⟨CriticalDoubleFullGeometry.geometry i hi h2,native_normalization i hi h2,?_,finite_statement⟩
 intro q
 exact ⟨CriticalDoubleGeometry.normalized_root_square i q,
 CriticalNormalizationDiagram.normalized_root_generates i q⟩

end FourCorner.CriticalDoubleFull
#print axioms FourCorner.CriticalDoubleFull.native_normalization
#print axioms FourCorner.CriticalDoubleFull.finite_statement
#print axioms FourCorner.CriticalDoubleFull.prop_crit_double
