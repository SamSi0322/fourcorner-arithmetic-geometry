import AllPointSchemeProperties
import AffineChartPlaceEvaluation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false
namespace FourCorner.RestrictionUnramifiedTransport
open AlgebraicCurve AllPointStalkUnramified
universe u
variable {K F E F' E' : Type u} [Field K] [Field F] [Field E] [Field F'] [Field E']
  [Algebra K F] [Algebra K E] [Algebra K F'] [Algebra K E']
  [Algebra F E] [Algebra F' E'] [IsScalarTower K F E] [IsScalarTower K F' E']
  [FiniteDimensional F E] [FiniteDimensional F' E']

/-- Actual restricted valuation rings transport through BOTH specified field
comparisons and their proved actual inclusion diagram. -/
def baseValuationEquiv (e : F ≃ₐ[K] F') (g : E ≃ₐ[K] E')
    (hc : ∀ a:F,g (algebraMap F E a)=algebraMap F' E' (e a)) (w : Place K E) :
    (w.restrict F).toValuationSubring ≃+*
      ((Place.congrEquiv g.toRingEquiv g.commutes w).restrict F').toValuationSubring where
  toFun a := ⟨e a,by
    change g.symm (algebraMap F' E' (e a))∈w.toValuationSubring
    rw [←hc,AlgEquiv.symm_apply_apply]
    exact a.property⟩
  invFun b := ⟨e.symm b,by
    have hb : g.symm (algebraMap F' E' (b : F'))∈w.toValuationSubring := b.property
    have he : g (algebraMap F E (e.symm (b : F')))=algebraMap F' E' (b : F') := by
      simpa only [AlgEquiv.apply_symm_apply] using hc (e.symm (b : F'))
    have hh : algebraMap F E (e.symm (b : F'))=g.symm (algebraMap F' E' (b : F')) := by
      simpa only [AlgEquiv.symm_apply_apply] using congrArg g.symm he
    change algebraMap F E (e.symm (b : F'))∈w.toValuationSubring
    rw [hh]
    exact hb⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv b := Subtype.ext (e.apply_symm_apply b)
  map_mul' a b := Subtype.ext (e.map_mul a b)
  map_add' a b := Subtype.ext (e.map_add a b)

/-- Native formal-unramifiedness of every actual restriction is invariant
under the given TWO constant-field-compatible field maps. No different or
normalization-model comparison is assumed by the caller. -/
theorem all_restrictions (e : F ≃ₐ[K] F') (g : E ≃ₐ[K] E')
    (hc : ∀ a:F,g (algebraMap F E a)=algebraMap F' E' (e a))
    (h : ∀ w : Place K E,(Place.restrictInclusion F w).FormallyUnramified) :
    ∀ w' : Place K E',(Place.restrictInclusion F' w').FormallyUnramified := by
  intro w'
  let q := Place.congrEquiv g.toRingEquiv g.commutes
  obtain ⟨w,hw⟩ := q.surjective w'
  subst w'
  let eA := baseValuationEquiv e g hc w
  let eB := (AffineChartPlaceEvaluation.placeValuationAlgEquiv g w).toRingEquiv
  apply formallyUnramified_of_square (Place.restrictInclusion F' (q w))
    (Place.restrictInclusion F w) eA.symm eB.symm ?_ (h w)
  apply RingHom.ext
  intro b
  apply Subtype.ext
  change g.symm (algebraMap F' E' (b : F'))=algebraMap F E (e.symm (b : F'))
  apply g.injective
  rw [AlgEquiv.apply_symm_apply]
  simpa only [AlgEquiv.apply_symm_apply] using (hc (e.symm (b : F'))).symm

#print axioms baseValuationEquiv
#print axioms all_restrictions
end FourCorner.RestrictionUnramifiedTransport
