import RationalPlaceEvaluationUnique

noncomputable section
namespace FourCorner.RationalPlaceFibreHom
open AlgebraicCurve IsDedekindDomain ResiduePlaceEvaluation RationalPlaceEvaluationUnique
variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]
set_option maxHeartbeats 1500000

abbrev RationalFibre (v : Place K F) := {w : Place K E // w.restrict F=v ∧ w.IsRational}

/-- The base DVR acts on K by its actual rational-place evaluation. -/
abbrev FibreHom (v : Place K F) (hv : v.IsRational) :=
  letI := (evaluate v hv).toRingHom.toAlgebra
  Place.integralClosureAt E v →ₐ[v.toValuationSubring] K

/-- The actual integral closure embeds into the valuation ring of every
place above the original base place. -/
def closureInclusion (v : Place K F) (w : Place K E) (hw : w.restrict F=v) :
    Place.integralClosureAt E v →+* w.toValuationSubring :=
  (algebraMap (Place.integralClosureAt E v) E).codRestrict w.toValuationSubring.toSubring
    (Place.forall_mem_of_restrict_eq hw)

@[simp] theorem closureInclusion_coe (v : Place K F) (w : Place K E) (hw : w.restrict F=v)
    (b : Place.integralClosureAt E v) :
    (closureInclusion v w hw b : E)=algebraMap (Place.integralClosureAt E v) E b := rfl

/-- The induced map from the actual base valuation ring fixes K. -/
def baseInclusion (v : Place K F) (w : Place K E) (hw : w.restrict F=v) :
    v.toValuationSubring →ₐ[K] w.toValuationSubring where
  toRingHom := (closureInclusion v w hw).comp (algebraMap v.toValuationSubring (Place.integralClosureAt E v))
  commutes' c := by
    apply Subtype.ext
    change algebraMap (Place.integralClosureAt E v) E
      (algebraMap v.toValuationSubring (Place.integralClosureAt E v)
        (algebraMap K v.toValuationSubring c))=algebraMap K E c
    rw [←IsScalarTower.algebraMap_apply v.toValuationSubring (Place.integralClosureAt E v) E,
      IsScalarTower.algebraMap_apply v.toValuationSubring F E,
      ←IsScalarTower.algebraMap_apply K v.toValuationSubring F,
      ←IsScalarTower.algebraMap_apply K F E]

/-- Evaluation at an actual rational place above v, restricted to the
actual integral closure, fixes the original base reduction. -/
def closureEvaluation (v : Place K F) (hv : v.IsRational)
    (w : Place K E) (hw : w.restrict F=v) (hwr : w.IsRational) : FibreHom (E:=E) v hv := by
  letI := (evaluate v hv).toRingHom.toAlgebra
  refine { toRingHom := (evaluate w hwr).toRingHom.comp (closureInclusion v w hw)
           commutes' := ?_ }
  intro a
  change evaluate w hwr (closureInclusion v w hw
    (algebraMap v.toValuationSubring (Place.integralClosureAt E v) a))=evaluate v hv a
  exact AlgHom.congr_fun (algHom_unique v ((evaluate w hwr).comp (baseInclusion v w hw))
    (evaluate v hv)) a

theorem closureEvaluation_kernel (v : Place K F) (hv : v.IsRational)
    (w : Place K E) (hw : w.restrict F=v) (hwr : w.IsRational) :
    letI := (evaluate v hv).toRingHom.toAlgebra
    RingHom.ker (closureEvaluation v hv w hw hwr).toRingHom=(Place.fiberCenter E v hw).asIdeal := by
  letI := (evaluate v hv).toRingHom.toAlgebra
  ext b
  change evaluate w hwr (closureInclusion v w hw b)=0 ↔
    closureInclusion v w hw b∈IsLocalRing.maximalIdeal w.toValuationSubring
  exact RationalPlaceEvaluationUnique.evaluate_zero_iff_maximal w hwr _

/-- Equal closure evaluations force equal actual fibre places. -/
theorem closureEvaluation_injective (v : Place K F) (hv : v.IsRational) :
    Function.Injective (fun w : RationalFibre (E:=E) v =>
      closureEvaluation v hv w.val w.property.1 w.property.2) := by
  letI := (evaluate v hv).toRingHom.toAlgebra
  intro w w' h
  dsimp only at h
  apply Subtype.ext
  apply Place.eq_of_fiberCenter_eq w.property.1 w'.property.1
  apply HeightOneSpectrum.ext
  rw [←closureEvaluation_kernel v hv w.val w.property.1 w.property.2,
    ←closureEvaluation_kernel v hv w'.val w'.property.1 w'.property.2,h]

/-- Every map of the actual integral closure extending the original residue
map constructs an actual rational place above v, via its genuine maximal
ideal and the localization valuation ring. -/
theorem closureEvaluation_surjective (v : Place K F) (hv : v.IsRational) :
    Function.Surjective (fun w : RationalFibre (E:=E) v =>
      closureEvaluation v hv w.val w.property.1 w.property.2) := by
  letI := (evaluate v hv).toRingHom.toAlgebra
  intro g
  let A := v.toValuationSubring
  let B := Place.integralClosureAt E v
  have gbase (a : A) : g (algebraMap A B a)=evaluate v hv a := g.commutes a
  have gsurj : Function.Surjective g := by
    intro c
    refine ⟨algebraMap A B (algebraMap K A c),?_⟩
    rw [gbase]
    exact evaluate_constant v hv c
  haveI : (RingHom.ker g.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective g.toRingHom gsurj
  obtain ⟨pi,hpi⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hpieval : evaluate v hv pi=0 := by
    apply (RationalPlaceEvaluationUnique.evaluate_zero_iff_maximal v hv pi).mpr
    rw [IsLocalRing.mem_maximalIdeal,mem_nonunits_iff]
    exact hpi.not_isUnit
  have hker : RingHom.ker g.toRingHom ≠ ⊥ := by
    intro heq
    have hz : algebraMap A B pi=0 := by
      apply Ideal.mem_bot.mp
      rw [←heq]
      change g (algebraMap A B pi)=0
      rw [gbase,hpieval]
    exact hpi.ne_zero (Place.algebraMap_integralClosureAt_injective (F':=E) v
      (hz.trans (map_zero _).symm))
  let P : HeightOneSpectrum B := ⟨RingHom.ker g.toRingHom,inferInstance,hker⟩
  let w : Place K E := Place.placeOfPrime (v:=v) P
  letI : Algebra B w.toValuationSubring := by
    change Algebra B (HeightOneSpectrum.valuationSubringAtPrime E P)
    infer_instance
  letI : IsScalarTower B w.toValuationSubring E := by
    change IsScalarTower B (HeightOneSpectrum.valuationSubringAtPrime E P) E
    infer_instance
  haveI : IsLocalization P.asIdeal.primeCompl w.toValuationSubring := by
    change IsLocalization P.asIdeal.primeCompl (HeightOneSpectrum.valuationSubringAtPrime E P)
    exact Localization.subalgebra.isLocalization_ofField E P.asIdeal.primeCompl
      P.asIdeal.primeCompl_le_nonZeroDivisors
  have hg : ∀ t : P.asIdeal.primeCompl,IsUnit (g t) := by
    intro t
    apply isUnit_iff_ne_zero.mpr
    exact t.property
  let evRing : w.toValuationSubring →+* K := IsLocalization.lift (g:=g.toRingHom) hg
  have hconst (c : K) : algebraMap K w.toValuationSubring c=
      algebraMap B w.toValuationSubring (algebraMap A B (algebraMap K A c)) := by
    apply Subtype.ext
    change algebraMap K E c=algebraMap w.toValuationSubring E
      (algebraMap B w.toValuationSubring (algebraMap A B (algebraMap K A c)))
    rw [←IsScalarTower.algebraMap_apply B w.toValuationSubring E,
      ←IsScalarTower.algebraMap_apply A B E,
      IsScalarTower.algebraMap_apply A F E,
      ←IsScalarTower.algebraMap_apply K A F,
      ←IsScalarTower.algebraMap_apply K F E]
  let ev : w.toValuationSubring →ₐ[K] K :=
    { toRingHom := evRing
      commutes' := by
        intro c
        change evRing (algebraMap K w.toValuationSubring c)=c
        rw [hconst]
        change IsLocalization.lift hg (algebraMap B w.toValuationSubring
          (algebraMap A B (algebraMap K A c)))=c
        rw [IsLocalization.lift_eq]
        change g (algebraMap A B (algebraMap K A c))=c
        rw [gbase]
        exact evaluate_constant v hv c }
  have hwr : w.IsRational := isRational_of_algHom w ev
  have hw : w.restrict F=v := Place.restrict_placeOfPrime P
  refine ⟨⟨w,hw,hwr⟩,?_⟩
  apply AlgHom.ext
  intro b
  change evaluate w hwr (closureInclusion v w hw b)=g b
  rw [evaluate_eq w hwr ev]
  have hinc : closureInclusion v w hw b=algebraMap B w.toValuationSubring b := by
    apply Subtype.ext
    change algebraMap B E b=algebraMap w.toValuationSubring E (algebraMap B w.toValuationSubring b)
    exact IsScalarTower.algebraMap_apply B w.toValuationSubring E b
  rw [hinc]
  exact IsLocalization.lift_eq hg b

/-- Actual rational places above v are exactly the maps from its actual
integral closure extending the original residue evaluation. -/
def rationalFibreHomEquiv (v : Place K F) (hv : v.IsRational) :
    RationalFibre (E:=E) v ≃ FibreHom (E:=E) v hv :=
  Equiv.ofBijective _ ⟨closureEvaluation_injective v hv,closureEvaluation_surjective v hv⟩

@[simp] theorem rationalFibreHomEquiv_apply (v : Place K F) (hv : v.IsRational)
    (w : RationalFibre (E:=E) v) :
    rationalFibreHomEquiv v hv w=closureEvaluation v hv w.val w.property.1 w.property.2 := rfl

#print axioms closureEvaluation_surjective
#print axioms rationalFibreHomEquiv

#print axioms baseInclusion
#print axioms closureEvaluation
#print axioms closureEvaluation_injective
end FourCorner.RationalPlaceFibreHom
