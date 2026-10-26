import CriticalFieldCoordinates
import CriticalMapNaturality

noncomputable section
namespace FourCorner.CriticalFieldEquivalence
open CriticalDirectMap
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) (a b c : F)
    (hb : b^2-1=algebraMap k F i*(a^2-1))
    (hc : c^2-1=(1+algebraMap k F i)*(a^2-1))
    (ha : Transcendental k a)
    (hgen : IntermediateField.adjoin k (Set.range ![a,b,c])=⊤)

/-- The ACTUAL inverse field homomorphism has precisely the displayed
rational original-coordinate formulas, not just one-directional equations. -/
theorem inverse_coordinates :
    (equiv i hi h2 a b c hb hc ha hgen).symm a=
      inverseA (algebraMap k (CriticalEllipticField.field k) i) (CriticalEllipticField.x k) (CriticalEllipticField.y k) ∧
    (equiv i hi h2 a b c hb hc ha hgen).symm b=
      inverseB (algebraMap k (CriticalEllipticField.field k) i) (CriticalEllipticField.x k) (CriticalEllipticField.y k) ∧
    (equiv i hi h2 a b c hb hc ha hgen).symm c=
      inverseC (algebraMap k (CriticalEllipticField.field k) i) (CriticalEllipticField.x k) (CriticalEllipticField.y k) := by
  let f := equiv i hi h2 a b c hb hc ha hgen
  have h := original_coordinates i hi h2 a b c hb hc ha hgen
  rw [equiv_x,equiv_y] at h
  refine ⟨?_,?_,?_⟩
  · apply f.injective
    rw [AlgEquiv.apply_symm_apply]
    have hn := CriticalMapNaturality.inverseA f.toRingHom
      (algebraMap k (CriticalEllipticField.field k) i) (CriticalEllipticField.x k) (CriticalEllipticField.y k)
    change f _ = inverseA (f (algebraMap k (CriticalEllipticField.field k) i))
      (f (CriticalEllipticField.x k)) (f (CriticalEllipticField.y k)) at hn
    rw [AlgEquiv.commutes,equiv_x,equiv_y] at hn
    exact h.1.symm.trans hn.symm
  · apply f.injective
    rw [AlgEquiv.apply_symm_apply]
    have hn := CriticalMapNaturality.inverseB f.toRingHom
      (algebraMap k (CriticalEllipticField.field k) i) (CriticalEllipticField.x k) (CriticalEllipticField.y k)
    change f _ = inverseB (f (algebraMap k (CriticalEllipticField.field k) i))
      (f (CriticalEllipticField.x k)) (f (CriticalEllipticField.y k)) at hn
    rw [AlgEquiv.commutes,equiv_x,equiv_y] at hn
    exact h.2.1.symm.trans hn.symm
  · apply f.injective
    rw [AlgEquiv.apply_symm_apply]
    have hn := CriticalMapNaturality.inverseC f.toRingHom
      (algebraMap k (CriticalEllipticField.field k) i) (CriticalEllipticField.x k) (CriticalEllipticField.y k)
    change f _ = inverseC (f (algebraMap k (CriticalEllipticField.field k) i))
      (f (CriticalEllipticField.x k)) (f (CriticalEllipticField.y k)) at hn
    rw [AlgEquiv.commutes,equiv_x,equiv_y] at hn
    exact h.2.2.symm.trans hn.symm

end FourCorner.CriticalFieldEquivalence
#print axioms FourCorner.CriticalFieldEquivalence.inverse_coordinates
