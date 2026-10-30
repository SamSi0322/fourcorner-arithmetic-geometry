import ThetaCoverClassPortable.TwoTermExactness
import ThetaCoverClassPortable.TwoTermCokernel

namespace FourCorner.TwoTermFiniteness
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {K0 K1 P0 P1 M0 M1 : Type u}
variable [AddCommGroup K0] [AddCommGroup K1] [AddCommGroup P0] [AddCommGroup P1] [AddCommGroup M0] [AddCommGroup M1]
variable [Module R K0] [Module R K1] [Module R P0] [Module R P1] [Module R M0] [Module R M1]

/-- H0(P) and H1(K) finite imply H0(M) finite over noetherian R, from the
ACTUAL constructed connecting map and PROVED snake exactness. There is
NO finiteness assumption on any chart module K_i/P_i/M_i itself. -/
theorem finite_H0 [IsNoetherianRing R]
    (dK : K0 →ₗ[R] K1) (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (i0 : K0 →ₗ[R] P0) (i1 : K1 →ₗ[R] P1) (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hi1 : Function.Injective i1) (hp0 : Function.Surjective p0)
    (h0 : Function.Exact i0 p0) (h1 : Function.Exact i1 p1)
    (hsqK : dP.comp i0=i1.comp dK) (hsqM : dM.comp p0=p1.comp dP)
    [Module.Finite R (H0 dP)] [Module.Finite R (H1 dK)] : Module.Finite R (H0 dM) := by
  let delta := connecting dK dP dM i0 i1 p0 p1 hi1 hp0 h0 h1 hsqK hsqM
  let f := cyclesMap dP dM p0 p1 hsqM
  have hex : LinearMap.ker delta=LinearMap.range f :=
    connecting_kernel_eq_range dK dP dM i0 i1 p0 p1 hi1 hp0 h0 h1 hsqK hsqM
  letI : Module.Finite R (LinearMap.ker delta) :=
    Module.Finite.equiv (LinearEquiv.ofEq (LinearMap.range f) (LinearMap.ker delta) hex.symm)
  letI : IsNoetherian R (H1 dK) := inferInstance
  letI : Module.Finite R (LinearMap.range delta) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  letI : Module.Finite R ((H0 dM) ⧸ LinearMap.ker delta) :=
    Module.Finite.equiv delta.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker delta)

/-- Convenient actual two-term short-exact-row endpoint for two chart
presentations. Only COHOMOLOGY modules are assumed finite. -/
theorem finite_H0_H1 [IsNoetherianRing R]
    (dK : K0 →ₗ[R] K1) (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (i0 : K0 →ₗ[R] P0) (i1 : K1 →ₗ[R] P1) (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hi1 : Function.Injective i1) (hp0 : Function.Surjective p0) (hp1 : Function.Surjective p1)
    (h0 : Function.Exact i0 p0) (h1 : Function.Exact i1 p1)
    (hsqK : dP.comp i0=i1.comp dK) (hsqM : dM.comp p0=p1.comp dP)
    [Module.Finite R (H0 dP)] [Module.Finite R (H1 dK)] [Module.Finite R (H1 dP)] :
    Module.Finite R (H0 dM) ∧ Module.Finite R (H1 dM) :=
  ⟨finite_H0 dK dP dM i0 i1 p0 p1 hi1 hp0 h0 h1 hsqK hsqM,
    finite_H1 dP dM p0 p1 hsqM hp1⟩

#print axioms finite_H0
#print axioms finite_H0_H1
end
end FourCorner.TwoTermFiniteness
