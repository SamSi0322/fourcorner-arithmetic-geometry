import ThetaCoverClassPortable.AffinePointTopology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped Topology
namespace FourCorner.ThetaLocalSurvival.StrongTopology

universe u v w z
variable (R : Type u) [CommRing R]
variable (A : Type v) [CommRing A] [Algebra R A]
variable (K : Type w) [Field K] [Algebra R K] [TopologicalSpace K]
variable (a : A) (S : Type z) [CommRing S] [Algebra A S] [Algebra R S]
  [IsScalarTower R A S] [IsLocalization.Away a S]

/-- Restriction of a localization point lands in the actual principal open. -/
def localizationPointRestriction (f : S →ₐ[R] K) : {g : A →ₐ[R] K // g a ≠ 0} :=
  ⟨f.comp (Algebra.algHom R A S),
    ((IsLocalization.Away.algebraMap_isUnit a (S:=S)).map f.toMonoidHom).ne_zero⟩

/-- The inverse map is the universal localization lift, with no supplied point data. -/
def localizationPointLift (f : {g : A →ₐ[R] K // g a ≠ 0}) : S →ₐ[R] K :=
  IsLocalization.Away.liftAlgHom a (isUnit_iff_ne_zero.mpr f.2)

theorem localizationPointLift_algebraMap (f : {g : A →ₐ[R] K // g a ≠ 0}) (x : A) :
    localizationPointLift R A K a S f (algebraMap A S x) = f.1 x := by
  exact IsLocalization.Away.lift_eq a (isUnit_iff_ne_zero.mpr f.2) x

def localizationPointEquiv : (S →ₐ[R] K) ≃ {g : A →ₐ[R] K // g a ≠ 0} where
  toFun := localizationPointRestriction R A K a S
  invFun := localizationPointLift R A K a S
  left_inv := by
    intro f
    apply IsLocalization.algHom_ext (Submonoid.powers a)
    ext x
    exact localizationPointLift_algebraMap R A K a S _ x
  right_inv := by
    intro f
    apply Subtype.ext
    ext x
    exact localizationPointLift_algebraMap R A K a S f x

theorem localizationPointLift_mk' (f : {g : A →ₐ[R] K // g a ≠ 0})
    (r : A) (s : Submonoid.powers a) :
    localizationPointLift R A K a S f (IsLocalization.mk' S r s) = f.1 r / f.1 s := by
  have hn : f.1 s ≠ 0 := by
    obtain ⟨n, hn⟩ := s.2
    rw [←hn, map_pow]
    exact pow_ne_zero _ f.2
  apply (eq_div_iff hn).2
  have h := congrArg (localizationPointLift R A K a S f) (IsLocalization.mk'_spec S r s)
  simpa only [map_mul, localizationPointLift_algebraMap] using h

variable [IsTopologicalDivisionRing K]

theorem continuous_localizationPointRestriction :
    Continuous (localizationPointRestriction R A K a S) :=
  (continuous_precomposition (Algebra.algHom R A S)).subtype_mk _

theorem continuous_localizationPointLift : Continuous (localizationPointLift R A K a S) := by
  apply (continuous_affine_iff R S K _).2
  intro x
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers a) x
  simp_rw [localizationPointLift_mk']
  exact ((continuous_evaluation R A K r).comp continuous_subtype_val).div
    ((continuous_evaluation R A K s).comp continuous_subtype_val) (fun f => by
      obtain ⟨n, hn⟩ := s.2
      rw [←hn, map_pow]
      exact pow_ne_zero _ f.2)

/-- Principal-open affine charts agree with the strong topology of field-valued points. -/
def localizationPointHomeomorph : (S →ₐ[R] K) ≃ₜ {g : A →ₐ[R] K // g a ≠ 0} where
  toEquiv := localizationPointEquiv R A K a S
  continuous_toFun := continuous_localizationPointRestriction R A K a S
  continuous_invFun := continuous_localizationPointLift R A K a S

theorem isOpen_principalPointSet [T1Space K] :
    IsOpen {f : A →ₐ[R] K | f a ≠ 0} :=
  isClosed_singleton.isOpen_compl.preimage (continuous_evaluation R A K a)

end FourCorner.ThetaLocalSurvival.StrongTopology
