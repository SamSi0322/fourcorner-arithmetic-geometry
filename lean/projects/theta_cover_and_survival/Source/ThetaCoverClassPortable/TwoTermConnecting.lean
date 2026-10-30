import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic

namespace FourCorner.TwoTermFiniteness
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {K0 K1 P0 P1 M0 M1 : Type u}
variable [AddCommGroup K0] [AddCommGroup K1] [AddCommGroup P0] [AddCommGroup P1] [AddCommGroup M0] [AddCommGroup M1]
variable [Module R K0] [Module R K1] [Module R P0] [Module R P1] [Module R M0] [Module R M1]

abbrev H0 {X0 X1 : Type u} [AddCommGroup X0] [AddCommGroup X1] [Module R X0] [Module R X1]
    (d : X0 →ₗ[R] X1) := LinearMap.ker d
abbrev H1 {X0 X1 : Type u} [AddCommGroup X0] [AddCommGroup X1] [Module R X0] [Module R X1]
    (d : X0 →ₗ[R] X1) := X1 ⧸ LinearMap.range d

/-- Actual lifts of cycles in M, without a chosen linear section of p0. -/
def liftDomain (dM : M0 →ₗ[R] M1) (p0 : P0 →ₗ[R] M0) : Submodule R P0 :=
  LinearMap.ker (dM.comp p0)

def liftProjection (dM : M0 →ₗ[R] M1) (p0 : P0 →ₗ[R] M0) : liftDomain dM p0 →ₗ[R] H0 dM where
  toFun y := ⟨p0 (y : P0),y.property⟩
  map_add' y z := by apply Subtype.ext;exact map_add p0 _ _
  map_smul' r y := by apply Subtype.ext;exact map_smul p0 r (y : P0)

 theorem liftProjection_surjective (dM : M0 →ₗ[R] M1) (p0 : P0 →ₗ[R] M0)
    (hp0 : Function.Surjective p0) : Function.Surjective (liftProjection dM p0) := by
  intro x
  obtain ⟨y,hy⟩ := hp0 (x : M0)
  have hcycle : y∈liftDomain dM p0 := by
    change dM (p0 y)=0
    rw [hy]
    exact x.property
  exact ⟨⟨y,hcycle⟩,Subtype.ext hy⟩

/-- Actual first-row isomorphism K1≃ker(p1), derived from injection and
exactness. No module freeness/projectivity/linear splitting is assumed. -/
def rightKernelEquiv (i1 : K1 →ₗ[R] P1) (p1 : P1 →ₗ[R] M1)
    (hi1 : Function.Injective i1) (h1 : Function.Exact i1 p1) : K1 ≃ₗ[R] LinearMap.ker p1 := by
  let f := i1.codRestrict (LinearMap.ker p1) (fun k=>h1.apply_apply_eq_zero k)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    exact hi1 (congrArg Subtype.val h)
  · intro z
    obtain ⟨k,hk⟩ := (h1 (z : P1)).mp z.property
    exact ⟨k,Subtype.ext hk⟩

 def liftBoundary (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hsq : dM.comp p0=p1.comp dP) : liftDomain dM p0 →ₗ[R] LinearMap.ker p1 where
  toFun y := ⟨dP (y : P0),(LinearMap.congr_fun hsq (y : P0)).symm.trans y.property⟩
  map_add' y z := by apply Subtype.ext;exact map_add dP _ _
  map_smul' r y := by apply Subtype.ext;exact map_smul dP r (y : P0)

 def liftK1 (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (i1 : K1 →ₗ[R] P1) (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hi1 : Function.Injective i1) (h1 : Function.Exact i1 p1)
    (hsq : dM.comp p0=p1.comp dP) : liftDomain dM p0 →ₗ[R] K1 :=
  (rightKernelEquiv i1 p1 hi1 h1).symm.toLinearMap.comp (liftBoundary dP dM p0 p1 hsq)

 theorem liftK1_spec (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (i1 : K1 →ₗ[R] P1) (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hi1 : Function.Injective i1) (h1 : Function.Exact i1 p1)
    (hsq : dM.comp p0=p1.comp dP) (y : liftDomain dM p0) :
    i1 (liftK1 dP dM i1 p0 p1 hi1 h1 hsq y)=dP (y : P0) := by
  exact congrArg Subtype.val ((rightKernelEquiv i1 p1 hi1 h1).apply_symm_apply (liftBoundary dP dM p0 p1 hsq y))

 def rawConnecting (dK : K0 →ₗ[R] K1) (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (i1 : K1 →ₗ[R] P1) (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hi1 : Function.Injective i1) (h1 : Function.Exact i1 p1)
    (hsq : dM.comp p0=p1.comp dP) : liftDomain dM p0 →ₗ[R] H1 dK :=
  (LinearMap.range dK).mkQ.comp (liftK1 dP dM i1 p0 p1 hi1 h1 hsq)

 theorem rawConnecting_kills_kernel (dK : K0 →ₗ[R] K1) (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (i0 : K0 →ₗ[R] P0) (i1 : K1 →ₗ[R] P1) (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hi1 : Function.Injective i1) (h0 : Function.Exact i0 p0) (h1 : Function.Exact i1 p1)
    (hsqK : dP.comp i0=i1.comp dK) (hsqM : dM.comp p0=p1.comp dP) :
    LinearMap.ker (liftProjection dM p0)≤LinearMap.ker (rawConnecting dK dP dM i1 p0 p1 hi1 h1 hsqM) := by
  intro y hy
  have hy0 : p0 (y : P0)=0 := congrArg Subtype.val hy
  obtain ⟨a,ha⟩ := (h0 (y : P0)).mp hy0
  have hz : liftK1 dP dM i1 p0 p1 hi1 h1 hsqM y=dK a := by
    apply hi1
    calc
      i1 (liftK1 dP dM i1 p0 p1 hi1 h1 hsqM y)=dP (y : P0) := liftK1_spec _ _ _ _ _ _ _ _ _
      _ = dP (i0 a) := congrArg dP ha.symm
      _ = i1 (dK a) := LinearMap.congr_fun hsqK a
  change (LinearMap.range dK).mkQ (liftK1 dP dM i1 p0 p1 hi1 h1 hsqM y)=0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨a,hz.symm⟩

/-- The ACTUAL connecting morphism ker(dM)→coker(dK), descended through
ker(liftProjection). This uses a true quotient isomorphism, not a linear
section of the arbitrary surjection P0→M0. -/
def connecting (dK : K0 →ₗ[R] K1) (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (i0 : K0 →ₗ[R] P0) (i1 : K1 →ₗ[R] P1) (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hi1 : Function.Injective i1) (hp0 : Function.Surjective p0)
    (h0 : Function.Exact i0 p0) (h1 : Function.Exact i1 p1)
    (hsqK : dP.comp i0=i1.comp dK) (hsqM : dM.comp p0=p1.comp dP) : H0 dM →ₗ[R] H1 dK :=
  ((LinearMap.ker (liftProjection dM p0)).liftQ (rawConnecting dK dP dM i1 p0 p1 hi1 h1 hsqM)
    (rawConnecting_kills_kernel dK dP dM i0 i1 p0 p1 hi1 h0 h1 hsqK hsqM)).comp
      ((liftProjection dM p0).quotKerEquivOfSurjective (liftProjection_surjective dM p0 hp0)).symm.toLinearMap

 theorem connecting_on_lift (dK : K0 →ₗ[R] K1) (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (i0 : K0 →ₗ[R] P0) (i1 : K1 →ₗ[R] P1) (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hi1 : Function.Injective i1) (hp0 : Function.Surjective p0)
    (h0 : Function.Exact i0 p0) (h1 : Function.Exact i1 p1)
    (hsqK : dP.comp i0=i1.comp dK) (hsqM : dM.comp p0=p1.comp dP) (y : liftDomain dM p0) :
    connecting dK dP dM i0 i1 p0 p1 hi1 hp0 h0 h1 hsqK hsqM (liftProjection dM p0 y)=
      (LinearMap.range dK).mkQ (liftK1 dP dM i1 p0 p1 hi1 h1 hsqM y) := by
  unfold connecting
  rw [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

#print axioms connecting
#print axioms connecting_on_lift
end
end FourCorner.TwoTermFiniteness
