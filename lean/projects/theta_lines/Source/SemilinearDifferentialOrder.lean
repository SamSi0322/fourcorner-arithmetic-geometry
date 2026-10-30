import SemilinearPicAndEll
import HalfCanonicalDifferential
import ThetaVanishingDifferentialOrder

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicCurve KaehlerDifferential
namespace FourCorner.SemilinearDifferentialOrder
open DivisorPicClassification SemilinearPicAndEll
variable {K F : Type*} [Field K] [PerfectField K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]
local instance : HasCanonicalDivisor (K:=K) (F:=F) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀v : Place K F,v.DCoordGenerates := dCoordGenerates_of_isCurveOver

 def omegaCompatibility (g : SemilinearAut K F) :
    (SemilinearAut.toRingAut g).toRingHom.comp (algebraMap K F)=
      (algebraMap K F).comp (SemilinearAut.baseAut g).toRingHom :=
  RingHom.ext (SemilinearAut.commutes g)

/-- The true universal Kähler map of the actual base and field ring maps. -/
def omegaMap (g : SemilinearAut K F) : Ω[F⁄K] →ₛₗ[(SemilinearAut.baseAut g).toRingHom] Ω[F⁄K] :=
  KaehlerDifferential.mapOfRingHom (SemilinearAut.baseAut g).toRingHom
    (SemilinearAut.toRingAut g).toRingHom (omegaCompatibility g)

 theorem omegaMap_D (g : SemilinearAut K F) (f : F) :
    omegaMap g (D K F f)=D K F (g • f) := KaehlerDifferential.mapOfRingHom_D _ _ _ f

 theorem omegaMap_smul_F (g : SemilinearAut K F) (f : F) (ω : Ω[F⁄K]) :
    omegaMap g (f • ω)=(g • f) • omegaMap g ω :=
  KaehlerDifferential.mapOfRingHom_smul _ _ _ f ω

 theorem omegaMap_one (ω : Ω[F⁄K]) : omegaMap (1:SemilinearAut K F) ω=ω :=
  KaehlerDifferential.mapOfRingHom_id (omegaCompatibility 1) ω

 theorem omegaMap_mul (g h : SemilinearAut K F) (ω : Ω[F⁄K]) :
    omegaMap (g*h) ω=omegaMap g (omegaMap h ω) := by
  symm
  exact KaehlerDifferential.mapOfRingHom_comp_apply
    (τ:=(SemilinearAut.baseAut h).toRingHom) (φ:=(SemilinearAut.toRingAut h).toRingHom)
    (h:=omegaCompatibility h)
    (SemilinearAut.baseAut g).toRingHom (SemilinearAut.toRingAut g).toRingHom
    (omegaCompatibility g) (omegaCompatibility (g*h)) ω

 theorem omegaMap_ne_zero (g : SemilinearAut K F) {ω : Ω[F⁄K]} (hω : ω≠0) :
    omegaMap g ω≠0 := by
  intro h
  have hh:=omegaMap_mul g⁻¹ g ω
  rw [inv_mul_cancel,omegaMap_one,h,map_zero] at hh
  exact hω hh

/-- The image of the SOURCE chosen dCoord need NOT be the TARGET chosen
dCoord. Its actual target coefficient is a UNIT, proved from ord(tau pi)=1
and the genuine local derivative-unit theorem. -/
theorem mapped_dCoord_unit (g : SemilinearAut K F) (v : Place K F) :
    ∃u : (g • v).toValuationSubring,
      (u:F)=(g • v).differentialCoeff (omegaMap g v.dCoord) ∧ IsUnit u := by
  obtain ⟨π,hord,hcoord⟩ := Place.exists_ord_eq_one_and_dCoord_eq v
  have hπ : π≠0 := by
    intro h
    rw [h,v.ord_zero] at hord
    omega
  have hnew : (g • v).ord (g • π)=1 := (SemilinearAut.ord_smul g v π).trans hord
  obtain ⟨u,hu,hunit⟩ := ThetaVanishingDifferentialOrder.derivative_unit_of_order_one
    (g • v) (g • π) (by simpa using hπ) hnew
  refine ⟨u,?_,hunit⟩
  rw [hcoord,omegaMap_D]
  exact hu

 theorem ordDifferential_transport (g : SemilinearAut K F) (v : Place K F) (ω : Ω[F⁄K]) :
    (g • v).ordDifferential (omegaMap g ω)=v.ordDifferential ω := by
  by_cases hω : ω=0
  · simp only [hω,map_zero,Place.ordDifferential,Place.differentialCoeff_zero,Place.ord_zero]
  obtain ⟨u,hu,hunit⟩ := mapped_dCoord_unit g v
  have hu0 : (u:F)≠0 := by
    intro h
    exact hunit.ne_zero (Subtype.ext h)
  have hug : (g • v).ord (u:F)=0 := by
    have he : ((hunit.unit : (g • v).toValuationSubring):F)=(u:F) :=
      congrArg Subtype.val hunit.unit_spec
    rw [←he]
    exact (g • v).ord_coe_unit hunit.unit
  have hcoef : (g • v).differentialCoeff (omegaMap g ω)=
      (g • v.differentialCoeff ω)*(u:F) := by
    have hrepr : ω=v.differentialCoeff ω • v.dCoord :=
      (v.differentialCoeff_smul_dCoord ω).symm
    conv_lhs => rw [hrepr,omegaMap_smul_F,Place.differentialCoeff_smul,←hu]
  have hcoef0 : g • v.differentialCoeff ω≠0 := by simpa using coeff_ne_zero hω v
  unfold Place.ordDifferential
  rw [hcoef,(g • v).ord_mul hcoef0 hu0,hug,add_zero]
  exact SemilinearAut.ord_smul g v (v.differentialCoeff ω)

 theorem canonicalDivisor_transport (g : SemilinearAut K F) {ω : Ω[F⁄K]} (hω : ω≠0) :
    canonicalDivisorOf (omegaMap_ne_zero g hω)=g • canonicalDivisorOf hω := by
  ext w
  rw [canonicalDivisorOf_apply,SemilinearAut.divisor_smul_apply,canonicalDivisorOf_apply]
  have hh:=ordDifferential_transport g (g⁻¹ • w) ω
  rwa [smul_inv_smul] at hh

 theorem canonicalClass_fixed (g : SemilinearAut K F) : g • canonicalClass K F=canonicalClass K F := by
  obtain ⟨ω,hω⟩ := exists_ne (0:Ω[F⁄K])
  rw [canonicalClass_eq hω,pic_smul_class,←canonicalDivisor_transport g hω]
  exact canonical_class_independent (omegaMap_ne_zero g hω) hω

 theorem oddTheta_smul (g : SemilinearAut K F) {c : Pic K F} (hc : IsOddThetaClass c) :
    IsOddThetaClass (g • c) := by
  constructor
  · have hh:=congrArg (fun z:Pic K F=>g • z) hc.1
    rw [canonicalClass_fixed] at hh
    simpa only [two_nsmul,smul_add] using hh
  · rw [picEll_smul]
    exact hc.2

#print axioms mapped_dCoord_unit
#print axioms ordDifferential_transport
#print axioms canonicalClass_fixed
#print axioms oddTheta_smul
end FourCorner.SemilinearDifferentialOrder
