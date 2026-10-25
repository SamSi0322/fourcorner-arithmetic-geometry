import FourCorner.CommonRootSupport
import CommonPointSource

noncomputable section
namespace FourCorner.Genus17Support

/-- The manuscript's odd positive-odd-valuation support, as a finite set.
Positive rational valuation forces divisibility of the numerator. -/
def oddSupport (d : ℚ) : Finset ℕ :=
  d.num.natAbs.primeFactors.filter fun p =>
    p ≠ 2 ∧ 0 < padicValRat p d ∧ Odd (padicValRat p d)

theorem mem_oddSupport (d : ℚ) (p : ℕ) :
    p ∈ oddSupport d ↔ p.Prime ∧ p ≠ 2 ∧
      0 < padicValRat p d ∧ Odd (padicValRat p d) := by
  constructor
  · intro h
    obtain ⟨hp,h⟩ := Finset.mem_filter.mp h
    exact ⟨(Nat.mem_primeFactors.mp hp).1,h⟩
  · rintro ⟨hp,h2,hpos,hodd⟩
    refine Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp,?_,?_⟩,h2,hpos,hodd⟩
    · by_contra hn
      have hz := padicValNat.eq_zero_of_not_dvd hn
      simp only [padicValRat,padicValInt,hz,Nat.cast_zero,zero_sub] at hpos
      omega
    · intro hn
      have hz : d = 0 := Rat.num_eq_zero.mp (Int.natAbs_eq_zero.mp hn)
      subst d
      norm_num [padicValRat,padicValInt] at hpos

/-- Exact finite set K_t: choose the exponent of two and independently choose
a subset of the manuscript's finite odd support. -/
def twists (t : ℚ) : Finset ℚ :=
  ({false,true} : Finset Bool).biUnion fun e =>
    (oddSupport (t^2-1)).powerset.image fun S : Finset ℕ =>
      (if e then 2 else 1) * ∏ p ∈ S, (p : ℚ)

theorem mem_twists {t κ : ℚ} : κ ∈ twists t ↔
    ∃ (e : Bool) (S : Finset ℕ), S ⊆ oddSupport (t^2-1) ∧
      κ = (if e then 2 else 1) * ∏ p ∈ S, (p : ℚ) := by
  simp only [twists,Finset.mem_biUnion,Finset.mem_insert,Finset.mem_singleton,
    Finset.mem_image,Finset.mem_powerset]
  constructor
  · rintro ⟨e,he,S,hS,hκ⟩
    exact ⟨e,S,hS,hκ.symm⟩
  · rintro ⟨e,S,hS,hκ⟩
    refine ⟨e,?_,S,hS,hκ.symm⟩
    cases e <;> simp

/-- Every positive squarefree representative with the proved prime support
belongs to the exact finite K_t, including the independent exponent of two. -/
theorem squarefree_mem_twists {t : ℚ} {n : ℕ} (hn : Squarefree n)
    (hs : ∀ p : ℕ, p.Prime → p ∣ n → p = 2 ∨
      (0 < padicValRat p (t^2-1) ∧ Odd (padicValRat p (t^2-1)))) :
    (n : ℚ) ∈ twists t := by
  classical
  let S := n.primeFactors.erase 2
  have hS : S ⊆ oddSupport (t^2-1) := by
    intro p hp
    obtain ⟨hp2,hpn⟩ := Finset.mem_erase.mp hp
    obtain ⟨hpp,hpd,-⟩ := Nat.mem_primeFactors.mp hpn
    have h := hs p hpp hpd
    exact (mem_oddSupport _ _).mpr ⟨hpp,hp2,h.resolve_left hp2⟩
  apply mem_twists.mpr
  by_cases h2 : 2 ∈ n.primeFactors
  · refine ⟨true,S,hS,?_⟩
    have hprod := Finset.mul_prod_erase n.primeFactors (fun p => (p : ℚ)) h2
    have heq : (∏ p ∈ n.primeFactors, (p : ℚ)) = (n : ℚ) := by
      simpa only [Nat.cast_prod] using
        congrArg (fun a : ℕ => (a : ℚ)) (Nat.prod_primeFactors_of_squarefree hn)
    simpa only [S,ite_true,Nat.cast_ofNat] using heq.symm.trans hprod.symm
  · refine ⟨false,S,hS,?_⟩
    simp only [Bool.false_eq_true,ite_false,one_mul,S,Finset.erase_eq_of_notMem h2]
    simpa only [Nat.cast_prod] using
      congrArg (fun a : ℕ => (a : ℚ)) (Nat.prod_primeFactors_of_squarefree hn).symm

/-- The single ordered rational source chooses one global twist in the exact
finite set and a rational root, with no local squareclasses chosen separately. -/
theorem source_has_global_twist {t : ℚ} (ht : 1 < t) (S : CommonRootSource ℚ t) :
    ∃ κ ∈ twists t, 0 < κ ∧ ∃ z : ℚ, 0 < z ∧ S.ell = κ*z^2 ∧ z^2 = S.ell/κ := by
  obtain ⟨n,hn,hsf,hsupp,z,hz,hell⟩ := S.positive_squareclass_support ht
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  refine ⟨n,squarefree_mem_twists hsf hsupp,hnq,z,hz,hell,?_⟩
  rw [hell,mul_div_cancel_left₀ _ (ne_of_gt hnq)]

end FourCorner.Genus17Support
#print axioms FourCorner.Genus17Support.mem_oddSupport
#print axioms FourCorner.Genus17Support.squarefree_mem_twists
#print axioms FourCorner.Genus17Support.source_has_global_twist
