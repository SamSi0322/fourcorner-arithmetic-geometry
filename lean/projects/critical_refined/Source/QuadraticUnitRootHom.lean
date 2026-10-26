import QuadraticUnitResidueAlgebra

noncomputable section
namespace FourCorner.QuadraticUnitRootHom
open Polynomial Module QuadraticUnitIntegralClosure QuadraticUnitResidueAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The defining root relation gives all algebra maps out of the genuine
quadratic polynomial quotient, over arbitrary coefficient and target rings. -/
def quadraticHomRootEquiv (u : R) :
    (AdjoinRoot (X^2-C u) →ₐ[R] S) ≃ {z : S // z^2=algebraMap R S u} where
  toFun f := ⟨f (AdjoinRoot.root (X^2-C u)),by
    have hr : (AdjoinRoot.root (X^2-C u))^2=algebraMap R (AdjoinRoot (X^2-C u)) u := by
      have hh : aeval (AdjoinRoot.root (X^2-C u)) (X^2-C u)=0 := by
        rw [AdjoinRoot.aeval_eq,AdjoinRoot.mk_self]
      simpa only [map_sub,map_pow,aeval_X,aeval_C,sub_eq_zero] using hh
    rw [← map_pow,hr,f.commutes]⟩
  invFun z := AdjoinRoot.liftAlgHom (X^2-C u) (Algebra.ofId R S) z.val (by
    simpa [Algebra.ofId] using (sub_eq_zero.mpr z.property))
  left_inv f := by
    ext
    simp
  right_inv z := by
    apply Subtype.ext
    simp

variable {F E : Type*} [IsDomain R] [IsIntegrallyClosed R]
  [Field F] [Field E] [Algebra R F] [Algebra F E] [Algebra R E]
  [IsScalarTower R F E] [IsFractionRing R F] [FiniteDimensional F E]

/-- Maps from the actual integral closure to an actual residue algebra are
in bijection with literal roots of the reduced unit radicand. Generation of
the integral closure is proved by the trace argument, not an input premise. -/
def integralClosureHomRootEquiv (u : R) (r : E) (hr : r^2=algebraMap R E u)
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2)
    (hu : IsUnit u) (h2 : IsUnit (2 : R)) :
    ((integralClosure R E) →ₐ[R] S) ≃ {z : S // z^2=algebraMap R S u} := by
  let e := presentation u r hr hgen hdim hu h2
  let mapEquiv : ((integralClosure R E) →ₐ[R] S) ≃ (AdjoinRoot (X^2-C u) →ₐ[R] S) :=
    { toFun := fun f => f.comp e.toAlgHom
      invFun := fun f => f.comp e.symm.toAlgHom
      left_inv := by intro f; ext x; simp
      right_inv := by intro f; ext x; simp }
  exact mapEquiv.trans (quadraticHomRootEquiv u)

/-- The bijection evaluates the actual integral root, as required for
compatibility with residue-place evaluation. -/
theorem integralClosureHomRootEquiv_apply (u : R) (r : E) (hr : r^2=algebraMap R E u)
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2)
    (hu : IsUnit u) (h2 : IsUnit (2 : R)) (f : (integralClosure R E) →ₐ[R] S) :
    (integralClosureHomRootEquiv u r hr hgen hdim hu h2 f).val=
      f ⟨r,rootIntegral u r hr⟩ := by
  change f (presentation u r hr hgen hdim hu h2 (AdjoinRoot.root (X^2-C u)))=_
  congr 1
  apply Subtype.ext
  exact presentation_root u r hr hgen hdim hu h2

theorem integralClosureHomRootEquiv_symm_root (u : R) (r : E) (hr : r^2=algebraMap R E u)
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2)
    (hu : IsUnit u) (h2 : IsUnit (2 : R)) (z : {z : S // z^2=algebraMap R S u}) :
    (integralClosureHomRootEquiv u r hr hgen hdim hu h2).symm z
      ⟨r,rootIntegral u r hr⟩=z.val := by
  have hh := congrArg Subtype.val ((integralClosureHomRootEquiv u r hr hgen hdim hu h2).apply_symm_apply z)
  rw [integralClosureHomRootEquiv_apply] at hh
  exact hh

#print axioms integralClosureHomRootEquiv_symm_root
#print axioms quadraticHomRootEquiv
#print axioms integralClosureHomRootEquiv
#print axioms integralClosureHomRootEquiv_apply
end FourCorner.QuadraticUnitRootHom
