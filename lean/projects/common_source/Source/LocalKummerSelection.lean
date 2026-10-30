import KummerBridge
import DyadicBridge
import CSFoundation.CommonSourceDyadicChart
import FourCorner.PadicResidueSquareBasic

noncomputable section
namespace FourCorner.CommonSource
open OrderedSplit

/-- Localization preserves the signed, ordered square classes. -/
def localSquareClassMap : Units.modPow ℚ 2 →* Units.modPow ℚ_[2] 2 :=
  Units.modPow.map (Rat.castHom ℚ_[2]).toMonoidHom 2

@[simp] theorem localSquareClassMap_scalar (a : ℚ) (ha : a ≠ 0) :
    localSquareClassMap (scalarClass a ha) =
      scalarClass (a : ℚ_[2]) (by exact_mod_cast ha) := by
  unfold localSquareClassMap scalarClass
  rw [Units.modPow.map_mk]
  apply congrArg QuotientGroup.mk
  apply Units.ext
  rfl

def localKummer (n : ℚ) (hn : n ≠ 0) (P : Point n) :
    Fin 3 → Units.modPow ℚ_[2] 2 :=
  fun i => localSquareClassMap (kummerDelta n hn (Multiplicative.ofAdd P) i)

@[simp] theorem localKummer_zero (n : ℚ) (hn : n ≠ 0) :
    localKummer n hn 0 = 1 := by
  ext i
  simp [localKummer, show (0 : Point n) = O n from rfl]

theorem localKummer_add (n : ℚ) (hn : n ≠ 0) (P Q : Point n) :
    localKummer n hn (P+Q) = localKummer n hn P * localKummer n hn Q := by
  ext i
  simp only [localKummer, kummerDelta_add, Pi.mul_apply, map_mul]

/-- This is proved for the actual rational subgroup H, including infinity. -/
theorem localKummer_H (n : ℤ) (hn : n ≠ 0) (P : Point (n : ℚ))
    (hP : P ∈ H n hn) : localKummer (n : ℚ) (by exact_mod_cast hn) P = 1 := by
  cases P with
  | zero => exact localKummer_zero _ _
  | some x y he =>
    have hv := (some_mem_H_iff n hn x y he).mp hP
    have hE : CongruentEquation (n : ℚ) x y :=
      (congruentEquation_iff_weierstrass _ _ _).mpr he.left
    have heq : y^2=x*(x-n)*(x+n) := hE
    have hsq := commonSourceDyadic_rational_local_squares n x y heq hv
    let chart := commonSourceDyadicOfRat n x y heq hv
    have hnrm : ‖(n : ℚ_[2])‖ ≤ 1 := Padic.norm_int_le_one n
    have hx : x ≠ 0 := by
      intro hz
      simp [hz] at hv
    have hxm : x-(n:ℚ) ≠ 0 := by
      intro hz
      apply (chart.offsets_ne_zero hnrm).1
      change (x:ℚ_[2])-(n:ℚ_[2])=0
      exact_mod_cast hz
    have hxp : x+(n:ℚ) ≠ 0 := by
      intro hz
      apply (chart.offsets_ne_zero hnrm).2
      change (x:ℚ_[2])+(n:ℚ_[2])=0
      exact_mod_cast hz
    have hf : WeierstrassCurve.Affine.Point.some x y he =
        finitePoint (by exact_mod_cast hn) hE := rfl
    rw [hf]
    ext i
    unfold localKummer
    rw [kummerDelta_finitePoint _ hE hx hxm hxp]
    fin_cases i
    · exact (localSquareClassMap_scalar x hx).trans
        ((scalarClass_eq_one_iff _ _).mpr hsq.1)
    · exact (localSquareClassMap_scalar (x-n) hxm).trans
        ((scalarClass_eq_one_iff _ _).mpr hsq.2.1)
    · exact (localSquareClassMap_scalar (x+n) hxp).trans
        ((scalarClass_eq_one_iff _ _).mpr hsq.2.2)

/-- -1 is not a square in the actual completed field, by reduction modulo 4. -/
theorem dyadic_neg_one_not_square : ¬ IsSquare (-1 : ℚ_[2]) := by
  intro hs
  have hi : IsSquare (-1 : ℤ_[2]) := (padicInt_isSquare_coe_iff _).mp hs
  have hr := hi.map (PadicInt.toZModPow 2)
  have hbad : ¬ IsSquare (-1 : ZMod 4) := by decide
  apply hbad
  simpa using hr

theorem dyadic_two_not_square : ¬ IsSquare (2 : ℚ_[2]) := by
  intro hs
  obtain ⟨k,hk⟩ := commonRoot_even_val_of_isSquare hs
  have hv : (2 : ℚ_[2]).valuation = 1 := Padic.valuation_p
  rw [hv] at hk
  omega

/-- The exact integral congruence supplies a local square via Hensel, not an
assumed square-class label. -/
theorem dyadic_square_of_int_mod_eight (n : ℤ) (hn : n % 8 = 1) :
    IsSquare (n : ℚ_[2]) := by
  have hd : (8 : ℤ) ∣ n-1 := by omega
  obtain ⟨k,hk⟩ := hd
  have heq : (n : ℚ_[2]) = 1 + 8*(k:ℚ_[2]) := by exact_mod_cast (by omega : n=1+8*k)
  rw [heq]
  apply padic_two_isSquare_one_add
  have hn8 : ‖(8 : ℚ_[2])‖ = 1/8 := by
    have h8 : (8 : ℚ_[2]) = 2^3 := by norm_num
    have h2 : ‖(2 : ℚ_[2])‖ = 1 / 2 := by simpa using (Padic.norm_p (p:=2))
    rw [h8,norm_pow,h2]
    norm_num
  rw [norm_mul,hn8]
  have hk1 := Padic.norm_int_le_one (p:=2) k
  nlinarith


/-- Restriction of local descent to genuine rational two-torsion has trivial
kernel. All three nonidentity points are treated in the fixed slot order. -/
theorem localKummer_twoTorsion_kernel (n : ℚ) (hn : n ≠ 0) (P : Point n)
    (hP : 2 • P = 0) (hd : localKummer n hn P = 1) : P = 0 := by
  rcases (two_torsion_iff hn P).mp hP with h | h | h | h
  · exact h
  · rw [h] at hd
    have hh := congrFun hd 0
    have hc : scalarClass (-1 : ℚ_[2]) (by norm_num) = 1 := by
      simpa [localKummer,kummerDelta_T0] using hh
    exact False.elim (dyadic_neg_one_not_square ((scalarClass_eq_one_iff _ _).mp hc))
  · rw [h] at hd
    have hh := congrFun hd 1
    have hc : scalarClass (2 : ℚ_[2]) (by norm_num) = 1 := by
      simpa [localKummer,kummerDelta_Tplus] using hh
    exact False.elim (dyadic_two_not_square ((scalarClass_eq_one_iff _ _).mp hc))
  · rw [h] at hd
    have hh := congrFun hd 2
    have hc : scalarClass (2 : ℚ_[2]) (by norm_num) = 1 := by
      simpa [localKummer,kummerDelta_Tminus] using hh
    exact False.elim (dyadic_two_not_square ((scalarClass_eq_one_iff _ _).mp hc))

theorem localKummer_sub (n : ℚ) (hn : n ≠ 0) (P Q : Point n) :
    localKummer n hn (P-Q) = localKummer n hn P / localKummer n hn Q := by
  ext i
  unfold localKummer
  change localSquareClassMap (kummerDelta n hn
    (Multiplicative.ofAdd P / Multiplicative.ofAdd Q) i) = _
  simp only [map_div, Pi.div_apply]

theorem localKummer_twoTorsion_injective (n : ℚ) (hn : n ≠ 0) (P Q : Point n)
    (hP : 2 • P = 0) (hQ : 2 • Q = 0)
    (hd : localKummer n hn P = localKummer n hn Q) : P = Q := by
  apply sub_eq_zero.mp
  apply localKummer_twoTorsion_kernel n hn
  · rw [nsmul_sub,hP,hQ,sub_self]
  · rw [localKummer_sub,hd,div_self']

def localCommonClass (n : ℚ) (hn : n ≠ 0) : Fin 3 → Units.modPow ℚ_[2] 2 :=
  fun i => localSquareClassMap (commonKummerClass n hn i)

theorem localCommonClass_one (n : ℚ) (hn : n ≠ 0) (hs : IsSquare (n : ℚ_[2])) :
    localCommonClass n hn = localKummer n hn (T0 n hn) := by
  have hn2 : (n : ℚ_[2]) ≠ 0 := by exact_mod_cast hn
  have hc : scalarClass (n : ℚ_[2]) hn2 = 1 := (scalarClass_eq_one_iff _ _).mpr hs
  have hneg : scalarClass (-(n : ℚ_[2])) (neg_ne_zero.mpr hn2) =
      scalarClass (-1 : ℚ_[2]) (by norm_num) := by
    have hmul := scalarClass_mul (-1 : ℚ_[2]) (n : ℚ_[2]) (by norm_num) hn2
    simpa [hc] using hmul.symm
  ext i
  fin_cases i <;> simp [localCommonClass,commonKummerClass,localKummer,kummerDelta_T0,hneg,hc]

theorem localCommonClass_seven (n : ℚ) (hn : n ≠ 0)
    (hs : IsSquare (-(n : ℚ_[2]))) : localCommonClass n hn = 1 := by
  have hn2 : (n : ℚ_[2]) ≠ 0 := by exact_mod_cast hn
  have hc := (scalarClass_eq_one_iff (-(n : ℚ_[2])) (neg_ne_zero.mpr hn2)).mpr hs
  ext i
  fin_cases i <;> simp [localCommonClass,commonKummerClass,hc]

/-- Any decomposition over the actual subgroup H preserves the entire source
class in its torsion sum. No torsion-label selection is assumed. -/
theorem source_local_torsion_class (n : ℤ) (hn : n ≠ 0)
    (Q R U V τQ τR : Point (n : ℚ))
    (hU : U ∈ H n hn) (hV : V ∈ H n hn)
    (hQ : Q=U+τQ) (hR : R=V+τR)
    (hs : kummerDelta (n : ℚ) (by exact_mod_cast hn)
      (Multiplicative.ofAdd (Q+R)) = commonKummerClass (n : ℚ) (by exact_mod_cast hn)) :
    localKummer (n : ℚ) (by exact_mod_cast hn) (τQ+τR) =
      localCommonClass (n : ℚ) (by exact_mod_cast hn) := by
  have hloc : localKummer (n : ℚ) (by exact_mod_cast hn) (Q+R) =
      localCommonClass (n : ℚ) (by exact_mod_cast hn) := by
    ext i
    simp only [localKummer,hs,localCommonClass]
  rw [hQ,hR,show (U+τQ)+(V+τR)=(U+V)+(τQ+τR) by abel,
    localKummer_add,localKummer_add,localKummer_H n hn U hU,
    localKummer_H n hn V hV,one_mul,one_mul] at hloc
  exact hloc

/-- The n=1 mod 8 torsion sum is derived from actual ordered source descent. -/
theorem source_torsion_sum_one (n : ℤ) (hn : n ≠ 0) (hn8 : n%8=1)
    (Q R U V τQ τR : Point (n : ℚ))
    (hU : U ∈ H n hn) (hV : V ∈ H n hn)
    (hQ : Q=U+τQ) (hR : R=V+τR)
    (htQ : 2 • τQ=0) (htR : 2 • τR=0)
    (hs : kummerDelta (n : ℚ) (by exact_mod_cast hn)
      (Multiplicative.ofAdd (Q+R)) = commonKummerClass (n : ℚ) (by exact_mod_cast hn)) :
    τQ+τR=T0 (n : ℚ) (by exact_mod_cast hn) := by
  apply localKummer_twoTorsion_injective
  · rw [nsmul_add,htQ,htR,zero_add]
  · rw [two_nsmul,T0_add_self]
  · rw [source_local_torsion_class n hn Q R U V τQ τR hU hV hQ hR hs]
    apply localCommonClass_one
    simpa using dyadic_square_of_int_mod_eight n hn8

/-- The n=7 mod 8 torsion sum is zero, for the same actual source and subgroup. -/
theorem source_torsion_sum_seven (n : ℤ) (hn : n ≠ 0) (hn8 : n%8=7)
    (Q R U V τQ τR : Point (n : ℚ))
    (hU : U ∈ H n hn) (hV : V ∈ H n hn)
    (hQ : Q=U+τQ) (hR : R=V+τR)
    (htQ : 2 • τQ=0) (htR : 2 • τR=0)
    (hs : kummerDelta (n : ℚ) (by exact_mod_cast hn)
      (Multiplicative.ofAdd (Q+R)) = commonKummerClass (n : ℚ) (by exact_mod_cast hn)) :
    τQ+τR=0 := by
  apply localKummer_twoTorsion_kernel
  · rw [nsmul_add,htQ,htR,zero_add]
  · rw [source_local_torsion_class n hn Q R U V τQ τR hU hV hQ hR hs]
    apply localCommonClass_seven
    have hs := dyadic_square_of_int_mod_eight (-n) (by omega)
    simpa using hs

#print axioms localKummer_H
#print axioms localKummer_twoTorsion_injective
#print axioms source_torsion_sum_one
#print axioms source_torsion_sum_seven
end FourCorner.CommonSource
