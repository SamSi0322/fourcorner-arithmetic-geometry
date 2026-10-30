import HpDiagonalKernelRigidity

namespace FourCorner.HpQuadraticExpansion
open HpQuadraticRelations
noncomputable section
attribute [local instance] Classical.propDecidable

def pairIndex (i : Fin 10) : Pair :=
  ⟨(![0,0,0,0,1,1,1,2,2,3] i,![1,2,3,4,2,3,4,3,4,4] i),by fin_cases i <;> decide⟩
def pairEquiv : Fin 10 ≃ Pair := Equiv.ofBijective pairIndex (by decide)

variable {K : Type*} [CommRing K]

theorem sum_pairs (f : Pair → K) :
    ∑i,f i=∑i : Fin 10,f (pairIndex i) := (pairEquiv.sum_comp f).symm

def diagonal (d : Fin 5 → K) (M : Fin 5 → Fin 5 → K) (j : Fin 5) : K := ∑i,d i*(M j i)^2
def halfCross (d : Fin 5 → K) (M : Fin 5 → Fin 5 → K) (jk : Pair) : K := ∑i,d i*M jk.val.1 i*M jk.val.2 i

theorem quadratic_expansion (d : Fin 5 → K) (M : Fin 5 → Fin 5 → K) (x : Fin 5 → K) :
    (∑i,d i*(∑j,M j i*x j)^2)=
      (∑j,diagonal d M j*x j^2)+(∑jk,(2*halfCross d M jk)*x jk.val.1*x jk.val.2) := by
  rw [sum_pairs]
  simp only [diagonal,halfCross,Fin.sum_univ_five]
  norm_num only [Fin.sum_univ_succ,pairIndex,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.reduceFinMk,Fin.succ_mk]
  ring

theorem bilinear_expansion (d : Fin 5 → K) (M : Fin 5 → Fin 5 → K) (x y : Fin 5 → K) :
    (∑i,d i*(∑j,M j i*x j)*(∑j,M j i*y j))=
      (∑j,diagonal d M j*x j*y j)+
      (∑jk,halfCross d M jk*(x jk.val.1*y jk.val.2+x jk.val.2*y jk.val.1)) := by
  rw [sum_pairs]
  simp only [diagonal,halfCross,Fin.sum_univ_five]
  norm_num only [Fin.sum_univ_succ,pairIndex,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.reduceFinMk,Fin.succ_mk]
  ring

#print axioms quadratic_expansion
#print axioms bilinear_expansion
end
end FourCorner.HpQuadraticExpansion
