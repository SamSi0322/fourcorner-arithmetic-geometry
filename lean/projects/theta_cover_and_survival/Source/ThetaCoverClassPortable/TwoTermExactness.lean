import ThetaCoverClassPortable.TwoTermConnecting

namespace FourCorner.TwoTermFiniteness
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {K0 K1 P0 P1 M0 M1 : Type u}
variable [AddCommGroup K0] [AddCommGroup K1] [AddCommGroup P0] [AddCommGroup P1] [AddCommGroup M0] [AddCommGroup M1]
variable [Module R K0] [Module R K1] [Module R P0] [Module R P1] [Module R M0] [Module R M1]

/-- The actual induced map on degree-zero cycles. -/
def cyclesMap (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hsqM : dM.comp p0=p1.comp dP) : H0 dP →ₗ[R] H0 dM where
  toFun z := ⟨p0 (z : P0),(LinearMap.congr_fun hsqM (z : P0)).trans
    ((congrArg p1 z.property).trans (map_zero p1))⟩
  map_add' z w := by apply Subtype.ext;exact map_add p0 _ _
  map_smul' r z := by apply Subtype.ext;exact map_smul p0 r (z : P0)

 theorem connecting_cycles_zero (dK : K0 →ₗ[R] K1) (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (i0 : K0 →ₗ[R] P0) (i1 : K1 →ₗ[R] P1) (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hi1 : Function.Injective i1) (hp0 : Function.Surjective p0)
    (h0 : Function.Exact i0 p0) (h1 : Function.Exact i1 p1)
    (hsqK : dP.comp i0=i1.comp dK) (hsqM : dM.comp p0=p1.comp dP) (z : H0 dP) :
    connecting dK dP dM i0 i1 p0 p1 hi1 hp0 h0 h1 hsqK hsqM (cyclesMap dP dM p0 p1 hsqM z)=0 := by
  let y : liftDomain dM p0 := ⟨(z : P0),(cyclesMap dP dM p0 p1 hsqM z).property⟩
  have hz : liftK1 dP dM i1 p0 p1 hi1 h1 hsqM y=0 := by
    apply hi1
    exact (liftK1_spec dP dM i1 p0 p1 hi1 h1 hsqM y).trans (z.property.trans (map_zero i1).symm)
  change connecting dK dP dM i0 i1 p0 p1 hi1 hp0 h0 h1 hsqK hsqM (liftProjection dM p0 y)=0
  rw [connecting_on_lift,hz,map_zero]

/-- The essential actual snake exactness, PROVED from the original rows
and squares, never supplied as an abstract connecting-map hypothesis. -/
theorem connecting_exact (dK : K0 →ₗ[R] K1) (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (i0 : K0 →ₗ[R] P0) (i1 : K1 →ₗ[R] P1) (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hi1 : Function.Injective i1) (hp0 : Function.Surjective p0)
    (h0 : Function.Exact i0 p0) (h1 : Function.Exact i1 p1)
    (hsqK : dP.comp i0=i1.comp dK) (hsqM : dM.comp p0=p1.comp dP) :
    Function.Exact (cyclesMap dP dM p0 p1 hsqM)
      (connecting dK dP dM i0 i1 p0 p1 hi1 hp0 h0 h1 hsqK hsqM) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := liftProjection_surjective dM p0 hp0 x
    have hraw : (LinearMap.range dK).mkQ (liftK1 dP dM i1 p0 p1 hi1 h1 hsqM y)=0 :=
      (connecting_on_lift dK dP dM i0 i1 p0 p1 hi1 hp0 h0 h1 hsqK hsqM y).symm.trans
        ((congrArg (connecting dK dP dM i0 i1 p0 p1 hi1 hp0 h0 h1 hsqK hsqM) hy).trans hx)
    have hmem : liftK1 dP dM i1 p0 p1 hi1 h1 hsqM y∈LinearMap.range dK :=
      (Submodule.Quotient.mk_eq_zero _).mp hraw
    obtain ⟨a,ha⟩ := hmem
    have hz : dP ((y : P0)-i0 a)=0 := by
      calc
        dP ((y : P0)-i0 a)=dP (y : P0)-dP (i0 a) := map_sub dP _ _
        _ = i1 (liftK1 dP dM i1 p0 p1 hi1 h1 hsqM y)-i1 (dK a) :=
          congrArg₂ (·-·) (liftK1_spec dP dM i1 p0 p1 hi1 h1 hsqM y).symm (LinearMap.congr_fun hsqK a)
        _ = 0 := by rw [ha,sub_self]
    refine ⟨⟨(y : P0)-i0 a,hz⟩,?_⟩
    apply Subtype.ext
    change p0 ((y : P0)-i0 a)=(x : M0)
    rw [map_sub,h0.apply_apply_eq_zero,sub_zero]
    exact congrArg Subtype.val hy
  · rintro ⟨z,rfl⟩
    exact connecting_cycles_zero dK dP dM i0 i1 p0 p1 hi1 hp0 h0 h1 hsqK hsqM z

 theorem connecting_kernel_eq_range (dK : K0 →ₗ[R] K1) (dP : P0 →ₗ[R] P1) (dM : M0 →ₗ[R] M1)
    (i0 : K0 →ₗ[R] P0) (i1 : K1 →ₗ[R] P1) (p0 : P0 →ₗ[R] M0) (p1 : P1 →ₗ[R] M1)
    (hi1 : Function.Injective i1) (hp0 : Function.Surjective p0)
    (h0 : Function.Exact i0 p0) (h1 : Function.Exact i1 p1)
    (hsqK : dP.comp i0=i1.comp dK) (hsqM : dM.comp p0=p1.comp dP) :
    LinearMap.ker (connecting dK dP dM i0 i1 p0 p1 hi1 hp0 h0 h1 hsqK hsqM)=
      LinearMap.range (cyclesMap dP dM p0 p1 hsqM) :=
  (connecting_exact dK dP dM i0 i1 p0 p1 hi1 hp0 h0 h1 hsqK hsqM).linearMap_ker_eq

#print axioms connecting_cycles_zero
#print axioms connecting_exact
#print axioms connecting_kernel_eq_range
end
end FourCorner.TwoTermFiniteness
