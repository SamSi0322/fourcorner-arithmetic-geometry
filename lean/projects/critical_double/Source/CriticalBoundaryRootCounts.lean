import CriticalBoundaryCharacter
import CriticalSignPoints
import Mathlib.Data.Set.Card

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace FourCorner.CriticalBoundaryRootCounts
open CriticalElliptic23
variable {k : Type*} [Field k]

def ordinary (e:Fin 3→Bool) : Prop := e 2=Bool.xor (e 0) (e 1)
instance ordinaryDecidable (e:Fin 3→Bool) : Decidable (ordinary e) :=
  inferInstanceAs (Decidable (e 2=Bool.xor (e 0) (e 1)))
attribute [local instance] Classical.propDecidable
def residue (i:k) (e:Fin 3→Bool) : k :=
  if ordinary e then 4*(sign (e 0)*sign (e 1)) else i*(sign (e 0)*sign (e 1))

lemma sign_nonzero (e:Bool) : sign (k:=k) e≠0 := by cases e <;> simp [sign]
lemma sign_product (e1 e2:Bool) : sign (k:=k) (Bool.xor e1 e2)=sign e1*sign e2 := by
  cases e1 <;> cases e2 <;> simp [sign]

lemma ordinary_iff (e:Fin 3→Bool) (h2:(2:k)≠0) :
    ordinary e ↔ sign (k:=k) (e 2)=sign (e 0)*sign (e 1) := by
  rw [←sign_product]
  exact (sign_injective h2).eq_iff.symm

lemma sign_square (i:k) (hi:i^2 = -1) (e:Bool) : IsSquare (sign (k:=k) e) := by
  cases e
  · exact ⟨1,by simp [sign]⟩
  · exact ⟨i,by simpa [sign,pow_two] using hi.symm⟩

lemma residue_nonzero (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (e:Fin 3→Bool) : residue i e≠0 := by
  have hp:=mul_ne_zero (sign_nonzero (k:=k) (e 0)) (sign_nonzero (k:=k) (e 1))
  have h4:(4:k)≠0 := by convert pow_ne_zero 2 h2 using 1 <;> ring
  unfold residue
  split_ifs
  · exact mul_ne_zero h4 hp
  · exact mul_ne_zero (iota_nonzero i hi) hp

lemma residue_square_iff (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (e:Fin 3→Bool) :
    IsSquare (residue i e) ↔ ordinary e ∨ IsSquare i := by
  have hp:= (sign_square i hi (e 0)).mul (sign_square i hi (e 1))
  have hp0:=mul_ne_zero (sign_nonzero (k:=k) (e 0)) (sign_nonzero (k:=k) (e 1))
  by_cases ho:ordinary e
  · rw [residue,if_pos ho]
    have hs:IsSquare ((4:k)*(sign (e 0)*sign (e 1))) := by
      have hh : (4:k)=(2:k)^2 := by ring
      rw [hh]
      exact (IsSquare.sq (2:k)).mul hp
    exact ⟨fun _=>Or.inl ho,fun _=>hs⟩
  · rw [residue,if_neg ho]
    constructor
    · intro hs
      have hh:=hs.div hp
      have he:i*(sign (e 0)*sign (e 1))/(sign (e 0)*sign (e 1))=i := mul_div_cancel_right₀ _ hp0
      rw [he] at hh
      exact Or.inr hh
    · rintro (bad|hs)
      · exact (ho bad).elim
      · exact hs.mul hp

lemma card_square_roots (a:k) (ha:a≠0) (h2:(2:k)≠0) (hs:IsSquare a) :
    Nat.card {z:k //z^2=a}=2 := by
  classical
  obtain ⟨r,hr⟩:=hs
  have hr0:r≠0 := by intro hz;rw [hz,mul_zero] at hr;exact ha hr
  have hn:r≠-r := by
    intro he
    have hh:(2:k)*r=0 := by linear_combination he
    exact (mul_ne_zero h2 hr0) hh
  have he : ({z : k | z ^ 2 = a} : Set k) = ({r, -r} : Set k) := by
    ext z
    rw [hr,←pow_two r]
    exact sq_eq_sq_iff_eq_or_eq_neg
  change Nat.card (↑({z : k | z ^ 2 = a} : Set k))=2
  rw [Nat.card_congr (Equiv.setCongr he)]
  exact Set.ncard_pair hn

lemma card_nonsquare_roots (a:k) (hs:¬IsSquare a) : Nat.card {z:k //z^2=a}=0 := by
  haveI:IsEmpty {z:k //z^2=a} := ⟨by
    rintro ⟨r,hr⟩
    exact hs ⟨r,by simpa only [pow_two] using hr.symm⟩⟩
  exact Nat.card_of_isEmpty

/-- The explicit local equations over the EIGHT ORIGINAL signed projective
boundary points have16 or8 roots. The actual place-fibre comparison is a
separate required bridge before this can be the proposition's Bp clause. -/
theorem local_boundary_count (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    Nat.card (Σ e:Fin 3→Bool, {z:k //z^2=residue i e})=
      if IsSquare i then 16 else 8 := by
  classical
  haveI (e:Fin 3→Bool):Finite {z:k //z^2=residue i e} := by
    by_cases hs:IsSquare (residue i e)
    · have h:=card_square_roots _ (residue_nonzero i hi h2 e) h2 hs
      exact Nat.finite_of_card_ne_zero (by rw [h];decide)
    · haveI:IsEmpty {z:k //z^2=residue i e} := ⟨by
        rintro ⟨r,hr⟩;exact hs ⟨r,by simpa only [pow_two] using hr.symm⟩⟩
      infer_instance
  rw [Nat.card_sigma]
  by_cases hs:IsSquare i
  · rw [if_pos hs]
    have he(e:Fin 3→Bool):Nat.card {z:k //z^2=residue i e}=2 :=
      card_square_roots _ (residue_nonzero i hi h2 e) h2 ((residue_square_iff i hi h2 e).mpr (Or.inr hs))
    simp only [he,Finset.sum_const,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul]
    norm_num
  · rw [if_neg hs]
    have he(e:Fin 3→Bool):Nat.card {z:k //z^2=residue i e}=if ordinary e then 2 else 0 := by
      by_cases ho:ordinary e
      · rw [if_pos ho]
        exact card_square_roots _ (residue_nonzero i hi h2 e) h2 ((residue_square_iff i hi h2 e).mpr (Or.inl ho))
      · rw [if_neg ho]
        apply card_nonsquare_roots
        exact fun h=>(residue_square_iff i hi h2 e).mp h |>.elim ho hs
    simp only [he]
    decide

end FourCorner.CriticalBoundaryRootCounts
#print axioms FourCorner.CriticalBoundaryRootCounts.ordinary_iff
#print axioms FourCorner.CriticalBoundaryRootCounts.residue_square_iff
#print axioms FourCorner.CriticalBoundaryRootCounts.card_square_roots
#print axioms FourCorner.CriticalBoundaryRootCounts.local_boundary_count
