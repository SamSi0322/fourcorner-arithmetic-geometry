import HpCanonicalForms

namespace FourCorner.HpRootProductBasis
open AlgebraicCurve HpLiteralField HpFieldGeometry HpCanonicalForms
noncomputable section
variable (K : Type*) [Field K]
attribute [local instance] Classical.propDecidable

def monomial (p : K) (s : Finset (Fin 4)) : field K p := ∏ i ∈ s,root K p i

def rootSpan (p : K) : Submodule (RatFunc K) (field K p) :=
  Submodule.span (RatFunc K) (Set.range (monomial K p))

theorem monomial_mem (p : K) (s : Finset (Fin 4)) : monomial K p s ∈ rootSpan K p :=
  Submodule.subset_span ⟨s,rfl⟩

theorem one_mem (p : K) : (1 : field K p)∈rootSpan K p := by
  simpa [monomial] using monomial_mem K p ∅

theorem root_mul_monomial (p : K) (i : Fin 4) (s : Finset (Fin 4)) :
    root K p i * monomial K p s =
      if i∈s then algebraMap (RatFunc K) (field K p) (radicand K p i) * monomial K p (s.erase i)
      else monomial K p (insert i s) := by
  by_cases hi : i∈s
  · rw [if_pos hi]
    have hm : monomial K p s=root K p i * monomial K p (s.erase i) := by
      simpa [monomial] using (Finset.mul_prod_erase s (root K p) hi).symm
    rw [hm,← mul_assoc,← sq,root_sq]
  · rw [if_neg hi]
    simp [monomial,Finset.prod_insert hi]

theorem root_mul_mem (p : K) (i : Fin 4) {x : field K p} (hx : x∈rootSpan K p) :
    root K p i*x∈rootSpan K p := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s,rfl⟩ := hx
    rw [root_mul_monomial]
    split_ifs
    · simpa only [Algebra.smul_def] using (rootSpan K p).smul_mem (radicand K p i) (monomial_mem K p (s.erase i))
    · exact monomial_mem K p _
  | zero => simpa using (rootSpan K p).zero_mem
  | add x y hx hy ihx ihy => simpa [mul_add] using (rootSpan K p).add_mem ihx ihy
  | smul a x hx ih =>
    simpa [Algebra.smul_def,mul_left_comm] using (rootSpan K p).smul_mem a ih

/-- The literal sixteen products span the actual generated field. -/
theorem rootSpan_eq_top (p : K) : rootSpan K p=⊤ := by
  have hh (x : field K p) (hx : x∈Algebra.adjoin (RatFunc K) (Set.range (root K p))) :
      ∀z∈rootSpan K p,x*z∈rootSpan K p := by
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      exact fun z hz => root_mul_mem K p i hz
    | algebraMap a =>
      exact fun z hz => by simpa only [Algebra.smul_def] using (rootSpan K p).smul_mem a hz
    | add x y hx hy ihx ihy =>
      exact fun z hz => by simpa [add_mul] using (rootSpan K p).add_mem (ihx z hz) (ihy z hz)
    | mul x y hx hy ihx ihy =>
      exact fun z hz => by simpa [mul_assoc] using ihx (y*z) (ihy z hz)
  apply top_unique
  intro x _
  have hx : x∈Algebra.adjoin (RatFunc K) (Set.range (root K p)) := by
    rw [root_generates K p]
    trivial
  simpa using hh x hx 1 (one_mem K p)

variable [NeZero (2 : K)]

theorem monomials_linearIndependent (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    LinearIndependent (RatFunc K) (monomial K p) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [← rootSpan,rootSpan_eq_top]
  · rw [field_degree_sixteen K p hp ha hb]
    simp

/-- A genuine basis of the given degree-sixteen field; no replacement algebra is used. -/
def basis (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    Module.Basis (Finset (Fin 4)) (RatFunc K) (field K p) :=
  Module.Basis.mk (monomials_linearIndependent K p hp ha hb) (by rw [← rootSpan,rootSpan_eq_top])

@[simp] theorem basis_apply (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (s : Finset (Fin 4)) :
    basis K p hp ha hb s=monomial K p s := Module.Basis.mk_apply _ _ _

#print axioms rootSpan_eq_top
#print axioms monomials_linearIndependent
#print axioms basis
end
end FourCorner.HpRootProductBasis
