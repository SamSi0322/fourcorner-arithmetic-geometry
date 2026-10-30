import CriticalMapTranscendence
import CriticalEllipticEvaluation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

noncomputable section
namespace FourCorner.CriticalFieldEquivalence
open CriticalConicParameter CriticalQuarticCubic CriticalDirectMap
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
set_option autoImplicit false
set_option maxHeartbeats 1500000

private theorem num (S : IntermediateField k F) (n : ℕ) : (n : F) ∈ S := S.natCast_mem n

theorem inverse_coordinates_mem (S : IntermediateField k F) (i x y : F)
    (hi : i ∈ S) (hx : x ∈ S) (hy : y ∈ S) :
    inverseA i x y ∈ S ∧ inverseB i x y ∈ S ∧ inverseC i x y ∈ S := by
  have h1 : (1:F) ∈ S := S.one_mem
  have h2 : (2:F) ∈ S := by simpa only [Nat.cast_ofNat] using num S 2
  have h4 : (4:F) ∈ S := by simpa only [Nat.cast_ofNat] using num S 4
  have hs : scale i ∈ S := S.sub_mem h1 hi
  have hX : inverseX i x ∈ S := S.add_mem hi (S.mul_mem hs hx)
  have hL : inverseL i y ∈ S := S.mul_mem (S.mul_mem h4 hs) hy
  have hv : inverseV (inverseX i x) (inverseL i y) ∈ S :=
    S.div_mem (S.sub_mem hL (S.mul_mem h4 (S.sub_mem h1 hX)))
      (S.mul_mem h2 (S.sub_mem (S.toSubalgebra.pow_mem hX 2) h1))
  have hu : inverseU i x y ∈ S := S.add_mem hv hi
  have hD : denominator i (inverseU i x y) ∈ S := S.sub_mem (S.toSubalgebra.pow_mem hu 2) hi
  refine ⟨?_,?_,?_⟩
  · exact S.div_mem (S.add_mem (S.sub_mem (S.toSubalgebra.pow_mem hu 2) (S.mul_mem h2 hu)) hi) hD
  · exact S.div_mem (S.sub_mem (S.add_mem (S.neg_mem (S.toSubalgebra.pow_mem hu 2))
      (S.mul_mem (S.mul_mem h2 hi) hu)) hi) hD
  · exact S.div_mem (S.neg_mem (S.sub_mem (S.sub_mem
      (S.mul_mem hX (S.toSubalgebra.pow_mem (S.sub_mem hu hi) 2)) (S.add_mem h1 hi))
      (S.mul_mem h2 (S.sub_mem hu hi)))) hD

theorem shift_nonzero {a : F} (ha : Transcendental k a) : a^2-1 ≠ 0 := by
  intro h
  apply ha.pow (by decide : 0<2)
  rw [sub_eq_zero.mp h]
  exact isAlgebraic_one

/-- Direct birational field equivalence from THREE literal source
coordinates. The generator hypothesis is an ordinary function-field
presentation, not an assumed elliptic comparison or genus conclusion. -/
def equiv (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (a b c : F)
    (hb : b^2-1=algebraMap k F i*(a^2-1))
    (hc : c^2-1=(1+algebraMap k F i)*(a^2-1))
    (ha : Transcendental k a)
    (hgen : IntermediateField.adjoin k (Set.range ![a,b,c])=⊤) :
    CriticalEllipticField.field k ≃ₐ[k] F := by
  let I := algebraMap k F i
  have hiF : I^2 = -1 := by simpa only [map_pow,map_neg,map_one] using congrArg (algebraMap k F) hi
  have h2F : (2:F) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero (algebraMap k F)).mpr h2
  have hshift : a^2-1 ≠ 0 := shift_nonzero ha
  have ha1 : a ≠ 1 := by intro h; apply hshift; rw [h]; ring
  have he := elliptic_equation I a b c hiF h2F hb hc ha1
  have ht := CriticalMapTranscendence.x_transcendental I a b c
    (isAlgebraic_algebraMap (x := i)) hiF h2F hb hc hshift ha
  let f := CriticalEllipticEvaluation.embedding k (x I a b c) (y I a b c) he ht
  have hs : Function.Surjective f := by
    let S := f.fieldRange
    have hx : x I a b c ∈ S := ⟨CriticalEllipticField.x k,CriticalEllipticEvaluation.embedding_x k _ _ _ _⟩
    have hy : y I a b c ∈ S := ⟨CriticalEllipticField.y k,CriticalEllipticEvaluation.embedding_y k _ _ _ _⟩
    have hg := inverse_coordinates_mem S I (x I a b c) (y I a b c) (S.algebraMap_mem i) hx hy
    rw [inverseA_forward I a b c hiF h2F hb hc hshift,
      inverseB_forward I a b c hiF h2F hb hc hshift,
      inverseC_forward I a b c hiF h2F hb hc hshift] at hg
    have htop : S=⊤ := by
      apply top_unique
      rw [←hgen]
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨j,rfl⟩
      fin_cases j
      all_goals first | exact hg.1 | exact hg.2.1 | exact hg.2.2
    intro z
    have hz : z ∈ S := by rw [htop]; trivial
    exact hz
  exact AlgEquiv.ofBijective f ⟨f.injective,hs⟩

end FourCorner.CriticalFieldEquivalence
#print axioms FourCorner.CriticalFieldEquivalence.equiv
