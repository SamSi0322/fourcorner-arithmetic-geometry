import ThetaNativeLineGaloisSet
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.ThetaLineGaloisAlgebra
open ThetaLinesAbsoluteGalois ThetaLinesProjectiveLines

/-- The associated algebra is defined from the actual independent native line Galois set,
by genuine equivariant functions in its actual finite splitting field. No product enters here. -/
def associatedSubalgebra : Subalgebra ℚ (KLine → K) where
  carrier := {f | ∀ (σ : G) (L : KLine), f (σ • L) = σ (f L)}
  algebraMap_mem' q σ L := (σ.commutes q).symm
  zero_mem' σ L := (map_zero σ).symm
  one_mem' σ L := (map_one σ).symm
  add_mem' hf hg σ L := by
    simp only [Pi.add_apply]
    rw [hf σ L, hg σ L, map_add]
  mul_mem' hf hg σ L := by
    simp only [Pi.mul_apply]
    rw [hf σ L, hg σ L, map_mul]

abbrev Associated := associatedSubalgebra

instance associatedFinite : Module.Finite ℚ Associated :=
  Module.Finite.of_injective associatedSubalgebra.val.toLinearMap Subtype.val_injective
instance associatedReduced : IsReduced Associated :=
  isReduced_of_injective associatedSubalgebra.val Subtype.val_injective
instance associatedArtinian : IsArtinianRing Associated := isArtinian_of_tower ℚ inferInstance

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in
/-- Real finite étaleness of the independently defined associated line algebra. -/
instance associatedEtale : Algebra.Etale ℚ Associated := by
  apply (Algebra.Etale.iff_exists_algEquiv_prod ℚ Associated).mpr
  exact ⟨MaximalSpectrum Associated, inferInstance,
    (fun p => Associated ⧸ p.asIdeal), inferInstance, inferInstance,
    (IsArtinianRing.equivPi Associated).restrictScalars ℚ,
    fun p => ⟨inferInstance, inferInstance⟩⟩

def evaluation (L : KLine) : Associated →ₐ[ℚ] K :=
  (Pi.evalAlgHom ℚ (fun _ : KLine => K) L).comp associatedSubalgebra.val

/-- Geometric evaluation at the SAME actual native dual-projective line. -/
def geometricPoint (P : ActualLine) : Associated →ₐ[ℚ] Qbar :=
  splittingEmbedding.comp (evaluation (lineEquiv.symm P))

/-- Evaluation retains the original absolute Galois action, through its actual restriction. -/
theorem geometricPoint_absolute (σ : AbsoluteG) (P : ActualLine) :
    geometricPoint (σ • P) = σ.toAlgHom.comp (geometricPoint P) := by
  obtain ⟨L, rfl⟩ := lineEquiv.surjective P
  rw [lineEquiv_absolute]
  ext f
  change splittingEmbedding (f.1 (lineEquiv.symm (lineEquiv (restrictAbsolute σ • L)))) =
    σ (splittingEmbedding (f.1 (lineEquiv.symm (lineEquiv L))))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, f.2, restrictAbsolute_commutes]

/-- Canonical normalized coefficients are actual equivariant functions. -/
def coefficientFunction (i : Fin 3) : Associated :=
  ⟨fun L => coefficients L.1 i, by
    intro σ L
    change coefficients (ThetaLinesProjectiveClassification.mapLine σ.toRingHom L.1) i =
      σ (coefficients L.1 i)
    rcases L with ⟨L, hL⟩
    cases L <;> fin_cases i <;> simp [coefficients, ThetaLinesProjectiveClassification.mapLine]⟩

/-- Geometric evaluations distinguish the actual native lines, independently of the list. -/
theorem geometricPoint_injective : Function.Injective geometricPoint := by
  intro P Q h
  apply lineEquiv.symm.injective
  apply Subtype.ext
  apply geometricLine_injective
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨1, ?_⟩
  rw [one_smul]
  funext i
  have hi := DFunLike.congr_fun h (coefficientFunction i)
  exact splittingEmbedding.injective hi.symm
end FourCorner.ThetaLineGaloisAlgebra
