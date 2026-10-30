import ThetaCoverClassPortable.TwoTermConnecting

namespace FourCorner.TwoTermFiniteness
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {P0 P1 M0 M1 : Type u}
variable [AddCommGroup P0] [AddCommGroup P1] [AddCommGroup M0] [AddCommGroup M1]
variable [Module R P0] [Module R P1] [Module R M0] [Module R M1]

/-- The actual induced quotient map coker(dP)→coker(dM). -/
def cokerMap (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hsqM : dM.comp p0=p1.comp dP) : H1 dP →ₗ[R] H1 dM :=
  (LinearMap.range dP).liftQ ((LinearMap.range dM).mkQ.comp p1) (by
    rintro z ⟨y,rfl⟩
    change (LinearMap.range dM).mkQ (p1 (dP y))=0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨p0 y,LinearMap.congr_fun hsqM y⟩)

 theorem cokerMap_mk (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hsqM : dM.comp p0=p1.comp dP) (y : P1) :
    cokerMap dP dM p0 p1 hsqM ((LinearMap.range dP).mkQ y)=(LinearMap.range dM).mkQ (p1 y) := rfl

 theorem cokerMap_surjective (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hsqM : dM.comp p0=p1.comp dP) (hp1 : Function.Surjective p1) :
    Function.Surjective (cokerMap dP dM p0 p1 hsqM) := by
  intro x
  obtain ⟨m,hm⟩ := (LinearMap.range dM).mkQ_surjective x
  obtain ⟨p,hp⟩ := hp1 m
  refine ⟨(LinearMap.range dP).mkQ p,?_⟩
  rw [cokerMap_mk,hp]
  exact hm

/-- H1 finiteness transfers by the PROVED actual quotient surjection;
no noetherianity or finiteness of P_i/M_i is needed. -/
theorem finite_H1 (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hsqM : dM.comp p0=p1.comp dP) (hp1 : Function.Surjective p1)
    [Module.Finite R (H1 dP)] : Module.Finite R (H1 dM) :=
  Module.Finite.of_surjective (cokerMap dP dM p0 p1 hsqM) (cokerMap_surjective dP dM p0 p1 hsqM hp1)

#print axioms cokerMap
#print axioms cokerMap_surjective
#print axioms finite_H1
end
end FourCorner.TwoTermFiniteness
