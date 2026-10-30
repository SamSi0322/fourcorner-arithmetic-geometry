import ThetaCoverClassPortable.NativeSinglePoleCharts

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
open CategoryTheory AlgebraicGeometry AlgebraicCurve IntermediateField
namespace FourCorner.NativeSinglePoleCharts
open CurveModel
universe u
variable {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L]
  (t : L) [FiniteDimensional K⟮t⟯ L]

theorem finite_aeval_tChart : (Polynomial.aeval (R:=K) (tChart K t)).toRingHom.Finite := by
  have h1 : (aevalAdjoin K t).toRingHom.Finite :=
    RingHom.Finite.of_surjective _ (aevalAdjoin_surjective K t)
  have h2 : (algebraMap (Algebra.adjoin K ({t} : Set L)) (chartRing K ({t} : Set L))).Finite := by
    exact RingHom.finite_algebraMap.mpr inferInstance
  have he : (Polynomial.aeval (R:=K) (tChart K t)).toRingHom =
      (algebraMap (Algebra.adjoin K ({t} : Set L)) (chartRing K ({t} : Set L))).comp
        (aevalAdjoin K t).toRingHom := by
    apply RingHom.ext
    intro p
    apply Subtype.val_injective
    exact (Polynomial.aeval_algHom_apply (chartRing K ({t} : Set L)).val (tChart K t) p).symm
  rw [he]
  exact h2.comp h1

theorem injective_aeval_tChart (ht : Transcendental K t) :
    Function.Injective (Polynomial.aeval (R:=K) (tChart K t)) := by
  intro a b h
  apply (transcendental_iff_injective.mp ht)
  have h' := congrArg (fun q : chartRing K ({t} : Set L) => (q : L)) h
  exact (Polynomial.aeval_algHom_apply (chartRing K ({t} : Set L)).val (tChart K t) a).trans
    (h'.trans (Polynomial.aeval_algHom_apply (chartRing K ({t} : Set L)).val (tChart K t) b).symm)

variable [Fact (t ≠ 0)] [FiniteDimensional K⟮t⁻¹⟯ L]
  {X : Scheme.{u}} (i : X ≅ glued K t)

def zeroAlgebra : Algebra K Γ(X, U t i) :=
  ((zeroSectionsEquiv t i).symm.toRingHom.comp
    (algebraMap K (chartRing K ({t} : Set L)))).toAlgebra

def infinityAlgebra : Algebra K Γ(X, V t i) :=
  ((infinitySectionsEquiv t i).symm.toRingHom.comp
    (algebraMap K (chartRing K ({t⁻¹} : Set L)))).toAlgebra

def zeroSectionsAlgEquiv : letI := zeroAlgebra t i
    Γ(X, U t i) ≃ₐ[K] chartRing K ({t} : Set L) := by
  letI := zeroAlgebra t i
  exact AlgEquiv.ofRingEquiv (f:=zeroSectionsEquiv t i) (fun a =>
    (zeroSectionsEquiv t i).apply_symm_apply _)

def infinitySectionsAlgEquiv : letI := infinityAlgebra t i
    Γ(X, V t i) ≃ₐ[K] chartRing K ({t⁻¹} : Set L) := by
  letI := infinityAlgebra t i
  exact AlgEquiv.ofRingEquiv (f:=infinitySectionsEquiv t i) (fun a =>
    (infinitySectionsEquiv t i).apply_symm_apply _)

theorem finite_aeval_fSection : letI := zeroAlgebra t i
    (Polynomial.aeval (R:=K) (fSection t i)).toRingHom.Finite := by
  letI := zeroAlgebra t i
  have h := (RingHom.Finite.of_surjective (zeroSectionsEquiv t i).symm.toRingHom
    (zeroSectionsEquiv t i).symm.surjective).comp (finite_aeval_tChart t)
  have he := congrArg AlgHom.toRingHom
    (Polynomial.aeval_algHom (zeroSectionsAlgEquiv t i).symm.toAlgHom (tChart K t))
  exact he ▸ h

theorem finite_aeval_gSection : letI := infinityAlgebra t i
    (Polynomial.aeval (R:=K) (gSection t i)).toRingHom.Finite := by
  letI := infinityAlgebra t i
  have h := (RingHom.Finite.of_surjective (infinitySectionsEquiv t i).symm.toRingHom
    (infinitySectionsEquiv t i).symm.surjective).comp (finite_aeval_tChart t⁻¹)
  have he := congrArg AlgHom.toRingHom
    (Polynomial.aeval_algHom (infinitySectionsAlgEquiv t i).symm.toAlgHom (tInvChart K t))
  exact he ▸ h

theorem injective_aeval_fSection (ht : Transcendental K t) : letI := zeroAlgebra t i
    Function.Injective (Polynomial.aeval (R:=K) (fSection t i)) := by
  letI := zeroAlgebra t i
  intro p q hpq
  apply injective_aeval_tChart t ht
  have hp := Polynomial.aeval_algHom_apply (zeroSectionsAlgEquiv t i).toAlgHom (fSection t i) p
  have hq := Polynomial.aeval_algHom_apply (zeroSectionsAlgEquiv t i).toAlgHom (fSection t i) q
  change (Polynomial.aeval (zeroSectionsEquiv t i (fSection t i))) p=_ at hp
  change (Polynomial.aeval (zeroSectionsEquiv t i (fSection t i))) q=_ at hq
  rw [zeroSectionsEquiv_fSection] at hp hq
  exact hp.trans ((congrArg (zeroSectionsEquiv t i) hpq).trans hq.symm)

end FourCorner.NativeSinglePoleCharts
