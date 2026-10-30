import CommonFourDegree
import FiniteFiveIndependence

/-! The actual four-root field of the literal Hasse source, over every field
of characteristic different from two. No degree, genus, local solubility or
geometric isomorphism conclusion is inserted into its definition. -/
namespace FourCorner.HpLiteralField

open Polynomial IntermediateField
noncomputable section

variable (K : Type*) [Field K]

def poly (p : K) : Fin 4 → K[X]
  | 0 => C p*X
  | 1 => C (2*(p-1))*(X-1)
  | 2 => C (2*(p+1))*(X+1)
  | 3 => C (p-1)*X+C (p+1)

def radicand (p : K) (i : Fin 4) : RatFunc K := algebraMap K[X] (RatFunc K) (poly K p i)

def branch (p : K) : Fin 4 → K
  | 0 => 0
  | 1 => 1
  | 2 => -1
  | 3 => -(p+1)/(p-1)

def radical (p : K) (i : Fin 4) : AlgebraicClosure (RatFunc K) :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (RatFunc K) (AlgebraicClosure (RatFunc K)) (radicand K p i))
    (show 0<(2 : ℕ) by decide))

theorem radical_sq (p : K) (i : Fin 4) :
    radical K p i^2=algebraMap (RatFunc K) (AlgebraicClosure (RatFunc K)) (radicand K p i) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (RatFunc K) (AlgebraicClosure (RatFunc K)) (radicand K p i))
    (show 0<(2 : ℕ) by decide))

def field (p : K) : IntermediateField (RatFunc K) (AlgebraicClosure (RatFunc K)) :=
  IntermediateField.adjoin (RatFunc K) (Set.range (radical K p))

def root (p : K) (i : Fin 4) : field K p :=
  ⟨radical K p i,IntermediateField.subset_adjoin _ _ ⟨i,rfl⟩⟩

theorem root_sq (p : K) (i : Fin 4) : root K p i^2=algebraMap (RatFunc K) (field K p) (radicand K p i) := by
  apply Subtype.ext
  exact radical_sq K p i

theorem root_adjoin_eq_top (p : K) :
    IntermediateField.adjoin (RatFunc K) (Set.range (root K p))=⊤ := by
  apply IntermediateField.lift_injective (field K p)
  rw [IntermediateField.lift_adjoin,IntermediateField.lift_top]
  congr 1
  ext x
  simp only [Set.mem_image,Set.mem_range]
  constructor
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨root K p i,⟨i,rfl⟩,rfl⟩

theorem finite_over_line (p : K) : FiniteDimensional (RatFunc K) (field K p) := by
  classical
  letI : Fintype (Set.range (radical K p)) := (Set.finite_range (radical K p)).fintype
  apply IntermediateField.finiteDimensional_adjoin
  rintro x ⟨i,rfl⟩
  refine ⟨X^2-C (radicand K p i),monic_X_pow_sub_C _ (by decide),?_⟩
  simp [radical_sq]

variable [NeZero (2 : K)]

theorem poly_eval_self (p : K) (ha : p-1 ≠ 0) (i : Fin 4) : (poly K p i).eval (branch K p i)=0 := by
  fin_cases i <;> simp [poly,branch]
  field_simp
  ring

theorem poly_derivative_self (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (i : Fin 4) :
    (poly K p i).derivative.eval (branch K p i) ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne _
  fin_cases i
  · simpa [poly,derivative_mul] using hp
  · simpa [poly,derivative_mul] using mul_ne_zero h2 ha
  · simpa [poly,derivative_mul] using mul_ne_zero h2 hb
  · simpa [poly,derivative_mul] using ha

theorem last_eval_zero (p : K) (ha : p-1 ≠ 0) :
    (poly K p 0).eval (branch K p 3)= -p*(p+1)/(p-1) := by
  simp only [poly,branch,eval_mul,eval_C,eval_X]
  field_simp

theorem last_eval_one (p : K) (ha : p-1 ≠ 0) :
    (poly K p 1).eval (branch K p 3)= -4*p := by
  simp only [poly,branch,eval_mul,eval_C,eval_sub,eval_X,eval_one]
  field_simp
  ring

theorem last_eval_two (p : K) (ha : p-1 ≠ 0) :
    (poly K p 2).eval (branch K p 3)= -4*(p+1)/(p-1) := by
  simp only [poly,branch,eval_mul,eval_C,eval_add,eval_X,eval_one]
  field_simp
  ring

theorem poly_eval_other (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (i j : Fin 4) (hij : j ≠ i) : (poly K p j).eval (branch K p i) ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne _
  have h4 : (4 : K) ≠ 0 := by
    have he : (4 : K)=2*2 := by ring
    rw [he]
    exact mul_ne_zero h2 h2
  have h11 : (1 : K)+1 ≠ 0 := by intro h;apply h2;linear_combination h
  have hn11 : (-1 : K)-1 ≠ 0 := by intro h;apply h2;linear_combination -h
  fin_cases i <;> fin_cases j <;> simp only [Fin.mk.injEq] at hij <;> try contradiction
  all_goals dsimp only
  · simp [poly,branch,h2,ha]
  · simp [poly,branch,h2,hb,h11]
  · simpa [poly,branch] using hb
  · simpa [poly,branch] using hp
  · simp [poly,branch,h2,hb,h11]
  · have he : (poly K p 3).eval (branch K p 1)=2*p := by simp [poly,branch];ring
    change (poly K p 3).eval (branch K p 1) ≠ 0
    rw [he]
    exact mul_ne_zero h2 hp
  · simpa [poly,branch] using hp
  · simp [poly,branch,h2,ha,hn11]
  · have he : (poly K p 3).eval (branch K p 2)=2 := by simp [poly,branch];ring
    change (poly K p 3).eval (branch K p 2) ≠ 0
    rw [he]
    exact h2
  · change (poly K p 0).eval (branch K p 3) ≠ 0
    rw [last_eval_zero K p ha]
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hp) hb) ha
  · change (poly K p 1).eval (branch K p 3) ≠ 0
    rw [last_eval_one K p ha]
    exact mul_ne_zero (neg_ne_zero.mpr h4) hp
  · change (poly K p 2).eval (branch K p 3) ≠ 0
    rw [last_eval_two K p ha]
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr h4) hb) ha

theorem polynomial_product_nonsquare (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (S : Finset (Fin 4)) (hS : S.Nonempty) : ¬IsSquare (∏ i ∈ S,poly K p i) := by
  classical
  intro hsquare
  obtain ⟨i,hi⟩ := hS
  have hz : (∏ j ∈ S,poly K p j).eval (branch K p i)=0 := by
    rw [eval_prod]
    exact Finset.prod_eq_zero hi (poly_eval_self K p ha i)
  exact FiniteFiveIndependence.product_derivative_nonzero S (poly K p) i hi (branch K p i)
    (poly_eval_self K p ha i) (poly_derivative_self K p hp ha hb i)
    (fun j _ hji => poly_eval_other K p hp ha hb i j hji)
    (FiniteFiveIndependence.square_derivative_zero hsquare _ hz)

theorem radicand_product_nonsquare (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (S : Finset (Fin 4)) (hS : S.Nonempty) : ¬IsSquare (∏ i ∈ S,radicand K p i) := by
  classical
  intro h
  apply polynomial_product_nonsquare K p hp ha hb S hS
  apply (FiniteFiveIndependence.square_map_polynomial_iff _).mp
  simpa only [map_prod,radicand] using h

theorem field_degree_sixteen (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    Module.finrank (RatFunc K) (field K p)=16 := by
  have hRange : Set.range (radical K p)=
      {radical K p 0,radical K p 1,radical K p 2,radical K p 3} := by
    ext x
    simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> tauto
    · rintro (h | h | h | h)
      · exact ⟨0,h.symm⟩
      · exact ⟨1,h.symm⟩
      · exact ⟨2,h.symm⟩
      · exact ⟨3,h.symm⟩
  unfold field
  rw [hRange]
  apply CommonFourDegree.finrank_four_eq_sixteen_of_products (radicand K p) (radical K p)
    (radical_sq K p)
  · simpa only [map_ofNat] using (map_ne_zero (algebraMap K (RatFunc K))).mpr (NeZero.ne (2 : K))
  · exact radicand_product_nonsquare K p hp ha hb

#print axioms root_sq
#print axioms root_adjoin_eq_top
#print axioms finite_over_line
#print axioms radicand_product_nonsquare
#print axioms field_degree_sixteen

end
end FourCorner.HpLiteralField
