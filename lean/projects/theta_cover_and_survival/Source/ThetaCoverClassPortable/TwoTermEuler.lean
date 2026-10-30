import ThetaCoverClassPortable.TwoTermFinite
import ThetaCoverClassPortable.FiniteKernelRange
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace FourCorner.TwoTermFiniteness
variable {R : Type u} [Field R]
variable {K0 K1 P0 P1 M0 M1 : Type u}
variable [AddCommGroup K0] [AddCommGroup K1] [AddCommGroup P0] [AddCommGroup P1] [AddCommGroup M0] [AddCommGroup M1]
variable [Module R K0] [Module R K1] [Module R P0] [Module R P1] [Module R M0] [Module R M1]
variable (dK : K0 →ₗ[R] K1) (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
  (i0 : K0 →ₗ[R] P0) (i1 : K1 →ₗ[R] P1) (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
  (hi0 : Function.Injective i0) (hi1 : Function.Injective i1)
  (hp0 : Function.Surjective p0) (hp1 : Function.Surjective p1)
  (h0 : Function.Exact i0 p0) (h1 : Function.Exact i1 p1)
  (hsqK : dP.comp i0=i1.comp dK) (hsqM : dM.comp p0=p1.comp dP)

include hi0 in
 theorem cyclesMap_injective : Function.Injective (cyclesMap dK dP i0 i1 hsqK) := by
  intro x y h
  apply Subtype.ext
  exact hi0 (congrArg Subtype.val h)

include hi1 h0 h1 in
 theorem cyclesMap_exact : Function.Exact (cyclesMap dK dP i0 i1 hsqK)
    (cyclesMap dP dM p0 p1 hsqM) := by
  intro x
  constructor
  · intro hx
    have hx0 : p0 (x : P0) = 0 := congrArg Subtype.val hx
    obtain ⟨k,hk⟩ := (h0 (x : P0)).mp hx0
    have hk0 : dK k=0 := by
      apply hi1
      have eq : dP (i0 k)=i1 (dK k) := LinearMap.congr_fun hsqK k
      rw [← eq,hk]
      exact x.property.trans (map_zero i1).symm
    exact ⟨⟨k,hk0⟩,Subtype.ext hk⟩
  · rintro ⟨k,rfl⟩
    apply Subtype.ext
    exact h0.apply_apply_eq_zero k

include hi1 hp0 h0 h1 in
 theorem connecting_coker_exact :
    Function.Exact (connecting dK dP dM i0 i1 p0 p1 hi1 hp0 h0 h1 hsqK hsqM)
      (cokerMap dK dP i0 i1 hsqK) := by
  intro x
  obtain ⟨k,rfl⟩ := (LinearMap.range dK).mkQ_surjective x
  constructor
  · intro hx
    have hx0 : i1 k ∈ LinearMap.range dP := (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨b,hb⟩ := hx0
    have hcycle : dM (p0 b)=0 := by
      have eq : dM (p0 b)=p1 (dP b) := LinearMap.congr_fun hsqM b
      rw [eq,hb]
      exact h1.apply_apply_eq_zero k
    let y : liftDomain dM p0 := ⟨b,hcycle⟩
    have hy : liftK1 dP dM i1 p0 p1 hi1 h1 hsqM y=k := by
      apply hi1
      exact (liftK1_spec dP dM i1 p0 p1 hi1 h1 hsqM y).trans hb
    refine ⟨liftProjection dM p0 y,?_⟩
    rw [connecting_on_lift,hy]
  · rintro ⟨z,hz⟩
    obtain ⟨y,hy⟩ := liftProjection_surjective dM p0 hp0 z
    rw [← hy,connecting_on_lift] at hz
    rw [← hz,cokerMap_mk]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨(y:P0),(liftK1_spec dP dM i1 p0 p1 hi1 h1 hsqM y).symm⟩

include hp0 h0 h1 in
 theorem cokerMap_exact : Function.Exact (cokerMap dK dP i0 i1 hsqK)
    (cokerMap dP dM p0 p1 hsqM) := by
  intro x
  obtain ⟨a,rfl⟩ := (LinearMap.range dP).mkQ_surjective x
  constructor
  · intro hx
    have hx0 : p1 a ∈ LinearMap.range dM := (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨m,hm⟩ := hx0
    obtain ⟨b,hb⟩ := hp0 m
    have hker : p1 (a-dP b)=0 := by
      have eq : dM (p0 b)=p1 (dP b) := LinearMap.congr_fun hsqM b
      rw [map_sub,← eq,hb,hm,sub_self]
    obtain ⟨k,hk⟩ := (h1 _).mp hker
    refine ⟨(LinearMap.range dK).mkQ k,?_⟩
    rw [cokerMap_mk]
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨-b,?_⟩
    rw [hk,map_neg]
    abel
  · rintro ⟨z,hz⟩
    rw [← hz]
    obtain ⟨k,rfl⟩ := (LinearMap.range dK).mkQ_surjective z
    rw [cokerMap_mk,cokerMap_mk,h1.apply_apply_eq_zero,map_zero]

include hi0 hi1 hp0 hp1 h0 h1 hsqK hsqM in
 theorem finite_and_euler
    [Module.Finite R (H0 dK)] [Module.Finite R (H1 dK)]
    [Module.Finite R (H0 dM)] [Module.Finite R (H1 dM)] :
    Module.Finite R (H0 dP) ∧ Module.Finite R (H1 dP) ∧
    (Module.finrank R (H0 dP) : ℤ)-Module.finrank R (H1 dP) =
      ((Module.finrank R (H0 dK) : ℤ)-Module.finrank R (H1 dK)) +
      ((Module.finrank R (H0 dM) : ℤ)-Module.finrank R (H1 dM)) := by
  let f0 := cyclesMap dK dP i0 i1 hsqK
  let f1 := cyclesMap dP dM p0 p1 hsqM
  let f2 := connecting dK dP dM i0 i1 p0 p1 hi1 hp0 h0 h1 hsqK hsqM
  let f3 := cokerMap dK dP i0 i1 hsqK
  let f4 := cokerMap dP dM p0 p1 hsqM
  have e1 : Function.Exact f0 f1 := cyclesMap_exact dK dP dM i0 i1 p0 p1 hi1 h0 h1 hsqK hsqM
  have e2 : Function.Exact f1 f2 := connecting_exact dK dP dM i0 i1 p0 p1 hi1 hp0 h0 h1 hsqK hsqM
  have e3 : Function.Exact f2 f3 := connecting_coker_exact dK dP dM i0 i1 p0 p1 hi1 hp0 h0 h1 hsqK hsqM
  have e4 : Function.Exact f3 f4 := cokerMap_exact dK dP dM i0 i1 p0 p1 hp0 h0 h1 hsqK hsqM
  letI : Module.Finite R (H0 dP) :=
    FourCorner.FiniteMapCohomology.finite_of_ker_le_range f1 f0 e1.linearMap_ker_eq.le
  letI : Module.Finite R (H1 dP) :=
    FourCorner.FiniteMapCohomology.finite_of_ker_le_range f4 f3 e4.linearMap_ker_eq.le
  refine ⟨inferInstance,inferInstance,?_⟩
  have hh0 := LinearMap.finrank_range_of_inj (cyclesMap_injective dK dP i0 i1 hi0 hsqK)
  have hh1 := f1.finrank_range_add_finrank_ker
  have hh2 := f2.finrank_range_add_finrank_ker
  have hh3 := f3.finrank_range_add_finrank_ker
  have hh4 := f4.finrank_range_add_finrank_ker
  rw [e1.linearMap_ker_eq] at hh1
  rw [e2.linearMap_ker_eq] at hh2
  rw [e3.linearMap_ker_eq] at hh3
  rw [e4.linearMap_ker_eq,LinearMap.range_eq_top.mpr
    (cokerMap_surjective dP dM p0 p1 hsqM hp1),finrank_top] at hh4
  change Module.finrank R (LinearMap.range f0)=Module.finrank R (H0 dK) at hh0
  omega
end FourCorner.TwoTermFiniteness
