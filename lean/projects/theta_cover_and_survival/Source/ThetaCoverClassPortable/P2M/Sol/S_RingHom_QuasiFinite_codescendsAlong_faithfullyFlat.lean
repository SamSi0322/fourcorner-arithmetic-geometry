import ThetaCoverClassPortable.QuasiFiniteFaithfullyFlat
open scoped TensorProduct

namespace P2MW.S_RingHom_QuasiFinite_codescendsAlong_faithfullyFlat
theorem solution :
    RingHom.CodescendsAlong RingHom.QuasiFinite RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.QuasiFinite.respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [RingHom.quasiFinite_algebraMap] at h' ⊢
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  letI : Module.FaithfullyFlat R S := h
  letI : Algebra.QuasiFinite S (S ⊗[R] T) := h'
  exact FourCorner.QuasiFiniteFpqc.quasiFinite_of_faithfullyFlat_baseChange (R:=R) (S:=S) (T:=T)
#print axioms solution
end P2MW.S_RingHom_QuasiFinite_codescendsAlong_faithfullyFlat
