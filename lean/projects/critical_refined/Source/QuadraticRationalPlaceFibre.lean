import RationalPlaceFibreHom
import QuadraticUnitRootHom

noncomputable section
namespace FourCorner.QuadraticRationalPlaceFibre
open AlgebraicCurve ResiduePlaceEvaluation RationalPlaceFibreHom
variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]
set_option maxHeartbeats 1500000

def rootInClosure (v : Place K F) (u : v.toValuationSubring) (r : E)
    (hr : r^2=algebraMap F E (u:F)) : Place.integralClosureAt E v :=
  ⟨r,QuadraticUnitResidueAlgebra.rootIntegral u r
    (hr.trans (IsScalarTower.algebraMap_apply v.toValuationSubring F E u).symm)⟩

/-- The actual given root as an integral element of an actual place above v. -/
def rootAtPlace (v : Place K F) (u : v.toValuationSubring) (r : E)
    (hr : r^2=algebraMap F E (u:F)) (w : Place K E) (hw : w.restrict F=v) :
    w.toValuationSubring := closureInclusion v w hw (rootInClosure v u r hr)

@[simp] theorem rootAtPlace_coe (v : Place K F) (u : v.toValuationSubring) (r : E)
    (hr : r^2=algebraMap F E (u:F)) (w : Place K E) (hw : w.restrict F=v) :
    (rootAtPlace v u r hr w hw : E)=r := rfl

/-- The actual rational-place fibre of a primitive degree-two unit extension
is in bijection with the literal roots of its original residue radicand.
Neither a fibre-root correspondence nor rationality of all fibre places is
assumed. The latter places are selected by their actual residue fields. -/
def rationalFibreRootEquiv (v : Place K F) (hv : v.IsRational)
    (u : v.toValuationSubring) (r : E) (hr : r^2=algebraMap F E (u:F))
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2)
    (hu : IsUnit u) (h2 : (2:K)≠0) :
    {w : Place K E // w.restrict F=v ∧ w.IsRational} ≃
      {z : K // z^2=evaluate v hv u} := by
  letI := (evaluate v hv).toRingHom.toAlgebra
  have h2A : IsUnit (2:v.toValuationSubring) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr h2).map (algebraMap K v.toValuationSubring)
  have hrA : r^2=algebraMap v.toValuationSubring E u :=
    hr.trans (IsScalarTower.algebraMap_apply v.toValuationSubring F E u).symm
  exact (rationalFibreHomEquiv v hv).trans
    (QuadraticUnitRootHom.integralClosureHomRootEquiv u r hrA hgen hdim hu h2A)

/-- The bijection computes the residue of the SAME actual given root r. -/
theorem rationalFibreRootEquiv_apply (v : Place K F) (hv : v.IsRational)
    (u : v.toValuationSubring) (r : E) (hr : r^2=algebraMap F E (u:F))
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2)
    (hu : IsUnit u) (h2 : (2:K)≠0)
    (w : {w : Place K E // w.restrict F=v ∧ w.IsRational}) :
    (rationalFibreRootEquiv v hv u r hr hgen hdim hu h2 w).val=
      evaluate w.val w.property.2 (rootAtPlace v u r hr w.val w.property.1) := by
  letI := (evaluate v hv).toRingHom.toAlgebra
  unfold rationalFibreRootEquiv
  rw [Equiv.trans_apply,QuadraticUnitRootHom.integralClosureHomRootEquiv_apply]
  rfl

/-- The inverse creates an actual rational place above v whose evaluation
of the original integral root is exactly the specified residue root. -/
theorem rationalFibreRootEquiv_symm_evaluation (v : Place K F) (hv : v.IsRational)
    (u : v.toValuationSubring) (r : E) (hr : r^2=algebraMap F E (u:F))
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2)
    (hu : IsUnit u) (h2 : (2:K)≠0) (z : {z : K // z^2=evaluate v hv u}) :
    let w := (rationalFibreRootEquiv v hv u r hr hgen hdim hu h2).symm z
    evaluate w.val w.property.2 (rootAtPlace v u r hr w.val w.property.1)=z.val := by
  have h := congrArg Subtype.val
    ((rationalFibreRootEquiv v hv u r hr hgen hdim hu h2).apply_symm_apply z)
  rw [rationalFibreRootEquiv_apply] at h
  exact h

#print axioms rationalFibreRootEquiv
#print axioms rationalFibreRootEquiv_apply
#print axioms rationalFibreRootEquiv_symm_evaluation
end FourCorner.QuadraticRationalPlaceFibre
