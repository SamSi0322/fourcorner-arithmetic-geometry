import EllipticCurves.WeakMordellWeil
import Mathlib.RingTheory.Polynomial.Quotient

open Polynomial

namespace FourCorner.OrderedSplit

variable {K : Type*} [Field K] {W : WeierstrassCurve.Affine K}

/-- Chinese remainder evaluation in the specified order of the three distinct roots. -/
noncomputable def orderedEval (r : Fin 3 → K) (hr : Function.Injective r)
    (hf : W.f = ∏ i : Fin 3, (X - C (r i))) : W.A ≃ₐ[K] (Fin 3 → K) := by
  let e : W.A ≃ₐ[K] (∀ i : Fin 3, K[X] ⧸ Ideal.span ({X - C (r i)} : Set K[X])) :=
    AlgEquiv.ofRingEquiv (f :=
      (Ideal.quotEquivOfEq (by
        rw [hf, Ideal.iInf_span_singleton (Polynomial.pairwise_coprime_X_sub_C hr)] :
        Ideal.span ({W.f} : Set K[X]) =
          ⨅ i : Fin 3, Ideal.span ({X - C (r i)} : Set K[X]))).trans <|
      Ideal.quotientInfRingEquivPiQuotient _ fun i j hij ↦
        (Ideal.isCoprime_span_singleton_iff _ _).mpr
          (Polynomial.pairwise_coprime_X_sub_C hr hij))
      fun _ ↦ rfl
  exact e.trans (AlgEquiv.piCongrRight fun i ↦ Polynomial.quotientSpanXSubCAlgEquiv (r i))

@[simp]
theorem orderedEval_mk (r : Fin 3 → K) (hr : Function.Injective r)
    (hf : W.f = ∏ i : Fin 3, (X - C (r i))) (q : K[X]) (i : Fin 3) :
    orderedEval r hr hf (AdjoinRoot.mk W.f q) i = q.eval (r i) := by
  rfl

theorem rootFactorization (r : Fin 3 → K)
    (hf : W.f = ∏ i : Fin 3, (X - C (r i))) :
    W.f = (X - C (r 0)) * (X - C (r 1)) * (X - C (r 2)) := by
  rw [hf, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp [mul_assoc]

theorem eval_f_eq_zero_iff (r : Fin 3 → K)
    (hf : W.f = ∏ i : Fin 3, (X - C (r i))) (x : K) :
    W.f.eval x = 0 ↔ ∃ i : Fin 3, x = r i := by
  classical
  simp [hf, Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

/-- The three labelled roots enumerate all roots, without changing their order. -/
noncomputable def rootSubtypeEquiv (r : Fin 3 → K) (hr : Function.Injective r)
    (hf : W.f = ∏ i : Fin 3, (X - C (r i))) :
    Fin 3 ≃ {x : K // W.f.eval x = 0} :=
  Equiv.ofBijective (fun i ↦ ⟨r i, (eval_f_eq_zero_iff r hf (r i)).mpr ⟨i, rfl⟩⟩)
    ⟨fun _ _ h ↦ hr (Subtype.mk.inj h), fun ⟨x, hx⟩ ↦ by
      obtain ⟨i, hi⟩ := (eval_f_eq_zero_iff r hf x).mp hx
      exact ⟨i, Subtype.ext hi.symm⟩⟩

@[simp]
theorem rootSubtypeEquiv_apply (r : Fin 3 → K) (hr : Function.Injective r)
    (hf : W.f = ∏ i : Fin 3, (X - C (r i))) (i : Fin 3) :
    (rootSubtypeEquiv r hr hf i).val = r i := rfl

theorem root_card_eq_three (r : Fin 3 → K) (hr : Function.Injective r)
    (hf : W.f = ∏ i : Fin 3, (X - C (r i))) :
    Nat.card {x : K // W.f.eval x = 0} = 3 := by
  rw [← Nat.card_congr (rootSubtypeEquiv r hr hf)]
  simp

#print axioms orderedEval
#print axioms orderedEval_mk
#print axioms rootFactorization
#print axioms rootSubtypeEquiv
#print axioms root_card_eq_three

end FourCorner.OrderedSplit
