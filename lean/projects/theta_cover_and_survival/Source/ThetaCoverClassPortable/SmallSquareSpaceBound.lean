import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
set_option autoImplicit false
open Polynomial Submodule
namespace FourCorner.DivisorPicClassification
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Over an algebraically closed base, a nonconstant field element is
transcendental. This is proved from its actual minimal polynomial. -/
theorem transcendental_of_not_mem_constant_span [IsAlgClosed K] {f : F}
    (hf : f∉Submodule.span K ({1}:Set F)) : Transcendental K f := by
  intro halg
  have hi := halg.isIntegral
  have hm := minpoly.monic hi
  have hd := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hi)
  have he := minpoly.aeval K f
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hd,hm.leadingCoeff,
    Polynomial.C_1,one_mul,Polynomial.aeval_add,Polynomial.aeval_X,Polynomial.aeval_C] at he
  apply hf
  apply Submodule.mem_span_singleton.mpr
  refine ⟨-(minpoly K f).coeff 0,?_⟩
  simp only [Algebra.smul_def,mul_one,map_neg]
  exact (eq_neg_of_add_eq_zero_left he).symm

 theorem finite_powers_independent {f : F} (hf : Transcendental K f) (n : ℕ) :
    LinearIndependent K (fun i : Fin n=>f^i.val) := by
  have hinj : Function.Injective (Polynomial.aeval f : K[X]→ₐ[K] F) :=
    transcendental_iff_injective.mp hf
  have hpoly := (Polynomial.basisMonomials K).linearIndependent.comp
    (fun i : Fin n=>i.val) Fin.val_injective
  have hp := hpoly.map' (Polynomial.aeval f).toLinearMap (LinearMap.ker_eq_bot.mpr hinj)
  change LinearIndependent K (fun i : Fin n=>(Polynomial.aeval f) ((Polynomial.basisMonomials K) i.val)) at hp
  simpa only [Polynomial.coe_basisMonomials,Polynomial.aeval_monomial,map_one,one_mul] using hp

/-- A PROVED special multiplication-space bound, sufficient for odd theta in
genus three. No Clifford inequality or product-space dimension theorem is an
input. If V contains 1 and all its products lie in an actual dimension-three
W, then V has dimension at most two. -/
theorem small_square_space_bound [IsAlgClosed K]
    (V W : Submodule K F) (h1 : (1:F)∈V)
    (hmul : ∀ x∈V,∀y∈V,x*y∈W) (hdim : Module.finrank K W=3) :
    Module.finrank K V≤2 := by
  classical
  letI : Module.Finite K W := Module.finite_of_finrank_pos (by omega)
  have hVW : V≤W := fun x hx=>by simpa using hmul x hx 1 h1
  letI : Module.Finite K V := Module.Finite.of_injective (Submodule.inclusion hVW)
    (Submodule.inclusion_injective hVW)
  by_cases hconst : V≤Submodule.span K ({1}:Set F)
  · have hh := Submodule.finrank_mono hconst
    rw [finrank_span_singleton (one_ne_zero:(1:F)≠0)] at hh
    omega
  · obtain ⟨f,hf,hfconst⟩ := SetLike.not_le_iff_exists.mp hconst
    have ht := transcendental_of_not_mem_constant_span hfconst
    have hpow : ∀i : Fin 3,f^i.val∈W := by
      intro i
      fin_cases i
      · simpa using hmul 1 h1 1 h1
      · simpa using hmul f hf 1 h1
      · simpa [pow_two] using hmul f hf f hf
    let w : Fin 3→W := fun i=>⟨f^i.val,hpow i⟩
    have hw : LinearIndependent K w :=
      LinearIndependent.of_comp W.subtype (finite_powers_independent ht 3)
    let b : Module.Basis (Fin 3) K W :=
      basisOfLinearIndependentOfCardEqFinrank hw (by simpa using hdim.symm)
    have hb : ∀i : Fin 3,(b i:F)=f^i.val := by
      intro i
      simp only [b,coe_basisOfLinearIndependentOfCardEqFinrank,w]
    have repr (g : F) (hg : g∈W) :
        ∃ a : Fin 3→K, algebraMap K F (a 0)+algebraMap K F (a 1)*f+
          algebraMap K F (a 2)*f^2=g := by
      refine ⟨fun i=>b.repr ⟨g,hg⟩ i,?_⟩
      have hh:=congrArg (fun z:W=>(z:F)) (b.sum_repr ⟨g,hg⟩)
      simpa only [Submodule.coe_sum,Submodule.coe_add,Submodule.coe_smul_of_tower,hb,
        Fin.sum_univ_three,Fin.val_zero,Fin.val_one,Fin.val_two,
        pow_zero,pow_one,Algebra.smul_def,mul_one] using hh
    have hspan : V≤Submodule.span K ({1,f}:Set F) := by
      intro g hg
      obtain ⟨a,ha⟩ := repr g (hVW hg)
      obtain ⟨c,hc⟩ := repr (f*g) (hmul f hf g hg)
      let p (v : Fin 3→K) : K[X] := C (v 0)+C (v 1)*X+C (v 2)*X^2
      have hpa : (Polynomial.aeval f) (p a)=g := by simpa [p] using ha
      have hpc : (Polynomial.aeval f) (p c)=f*g := by simpa [p] using hc
      have hp : X*p a=p c := (transcendental_iff_injective.mp ht) (by
        rw [map_mul,Polynomial.aeval_X,hpa,hpc])
      have ha2 : a 2=0 := by
        have hh:=congrArg (fun q:K[X]=>q.coeff 3) hp
        norm_num [p,Polynomial.coeff_X_mul,Polynomial.coeff_C_mul] at hh
        exact hh
      apply Submodule.mem_span_pair.mpr
      refine ⟨a 0,a 1,?_⟩
      simpa only [ha2,map_zero,zero_mul,add_zero,Algebra.smul_def,mul_one] using ha
    letI : Module.Finite K (Submodule.span K ({1,f}:Set F)) :=
      Module.Finite.span_of_finite K ((Set.finite_singleton f).insert 1)
    have hh := Submodule.finrank_mono hspan
    have hs := finrank_span_finset_le_card (R:=K) ({1,f}:Finset F)
    have hcard : ({1,f}:Finset F).card≤2 := by
      simpa using Finset.card_insert_le (1:F) ({f}:Finset F)
    change Module.finrank K (Submodule.span K (({1,f}:Finset F):Set F))≤({1,f}:Finset F).card at hs
    have hset : (({1,f}:Finset F):Set F)=({1,f}:Set F) := by ext z;simp
    rw [hset] at hs
    exact hh.trans (hs.trans hcard)

#print axioms small_square_space_bound
end FourCorner.DivisorPicClassification
