import CriticalFieldEquivalence

noncomputable section
namespace FourCorner.CriticalFieldEquivalence
open CriticalDirectMap
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) (a b c : F)
    (hb : b^2-1=algebraMap k F i*(a^2-1))
    (hc : c^2-1=(1+algebraMap k F i)*(a^2-1))
    (ha : Transcendental k a)
    (hgen : IntermediateField.adjoin k (Set.range ![a,b,c])=⊤)

/-- The isomorphism is the explicit original-coordinate rational map. -/
theorem equiv_x : equiv i hi h2 a b c hb hc ha hgen (CriticalEllipticField.x k)=
    x (algebraMap k F i) a b c := by
  have hiF : (algebraMap k F i)^2 = -1 := by simpa only [map_pow,map_neg,map_one] using congrArg (algebraMap k F) hi
  have h2F : (2:F) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero (algebraMap k F)).mpr h2
  have hs := shift_nonzero ha
  have ha1 : a ≠ 1 := by intro h; apply hs; rw [h]; ring
  have he := elliptic_equation (algebraMap k F i) a b c hiF h2F hb hc ha1
  have ht := CriticalMapTranscendence.x_transcendental (algebraMap k F i) a b c
    (isAlgebraic_algebraMap (x := i)) hiF h2F hb hc hs ha
  change CriticalEllipticEvaluation.embedding k _ _ he ht (CriticalEllipticField.x k)=_
  exact CriticalEllipticEvaluation.embedding_x k _ _ he ht

theorem equiv_y : equiv i hi h2 a b c hb hc ha hgen (CriticalEllipticField.y k)=
    y (algebraMap k F i) a b c := by
  have hiF : (algebraMap k F i)^2 = -1 := by simpa only [map_pow,map_neg,map_one] using congrArg (algebraMap k F) hi
  have h2F : (2:F) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero (algebraMap k F)).mpr h2
  have hs := shift_nonzero ha
  have ha1 : a ≠ 1 := by intro h; apply hs; rw [h]; ring
  have he := elliptic_equation (algebraMap k F i) a b c hiF h2F hb hc ha1
  have ht := CriticalMapTranscendence.x_transcendental (algebraMap k F i) a b c
    (isAlgebraic_algebraMap (x := i)) hiF h2F hb hc hs ha
  change CriticalEllipticEvaluation.embedding k _ _ he ht (CriticalEllipticField.y k)=_
  exact CriticalEllipticEvaluation.embedding_y k _ _ he ht

/-- Each ORIGINAL ordered source coordinate is fixed by the inverse
formulas in the actual isomorphism; no quotient-by-four map is used. -/
theorem original_coordinates :
    inverseA (algebraMap k F i)
      (equiv i hi h2 a b c hb hc ha hgen (CriticalEllipticField.x k))
      (equiv i hi h2 a b c hb hc ha hgen (CriticalEllipticField.y k))=a ∧
    inverseB (algebraMap k F i)
      (equiv i hi h2 a b c hb hc ha hgen (CriticalEllipticField.x k))
      (equiv i hi h2 a b c hb hc ha hgen (CriticalEllipticField.y k))=b ∧
    inverseC (algebraMap k F i)
      (equiv i hi h2 a b c hb hc ha hgen (CriticalEllipticField.x k))
      (equiv i hi h2 a b c hb hc ha hgen (CriticalEllipticField.y k))=c := by
  rw [equiv_x,equiv_y]
  have hiF : (algebraMap k F i)^2 = -1 := by simpa only [map_pow,map_neg,map_one] using congrArg (algebraMap k F) hi
  have h2F : (2:F) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero (algebraMap k F)).mpr h2
  exact ⟨inverseA_forward _ _ _ _ hiF h2F hb hc (shift_nonzero ha),
    inverseB_forward _ _ _ _ hiF h2F hb hc (shift_nonzero ha),
    inverseC_forward _ _ _ _ hiF h2F hb hc (shift_nonzero ha)⟩

end FourCorner.CriticalFieldEquivalence
#print axioms FourCorner.CriticalFieldEquivalence.equiv_x
#print axioms FourCorner.CriticalFieldEquivalence.equiv_y
#print axioms FourCorner.CriticalFieldEquivalence.original_coordinates
