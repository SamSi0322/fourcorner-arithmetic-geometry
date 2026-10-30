import ThetaCoverClassPortable.RankDataCompatibility
import Lean
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000
open Lean Elab Command Meta in
run_cmd do
  let originals : Array (Name × Expr) := #[
  (`Algebra.FinitePresentation.of_finitePresentation, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_1)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 55598290) "_hygCtx") "_hyg") 4)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 55598290) "_hygCtx") "_hyg") 7)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_1]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 55598290) "_hygCtx") "_hyg") 10)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Algebra [Lean.Level.param `u, Lean.Level.param `u_1])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 55598290) "_hygCtx") "_hyg") 14)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Module.FinitePresentation [Lean.Level.param `u, Lean.Level.param `u_1])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2))))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_1]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u, Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Algebra.FinitePresentation [Lean.Level.param `u, Lean.Level.param `u_1])
                      (Lean.Expr.bvar 5))
                    (Lean.Expr.bvar 4))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 5))
                    (Lean.Expr.bvar 3)))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 4))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 2))))
              (Lean.Expr.bvar 1))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))),
  (`Algebra.rankAtStalk_eq_of_isPushout, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_3)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_4)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2108817691) "_hygCtx") "_hyg") 16)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_3]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2108817691) "_hygCtx") "_hyg") 19)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_4]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2108817691) "_hygCtx") "_hyg") 22)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Algebra [Lean.Level.param `u_3, Lean.Level.param `u_4])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4]) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.Expr.forallE
            `R'
            (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_5)))
            (Lean.Expr.forallE
              `S'
              (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_6)))
              (Lean.Expr.forallE
                (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2108817691) "_hygCtx") "_hyg") 28)
                (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_5]) (Lean.Expr.bvar 1))
                (Lean.Expr.forallE
                  (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2108817691) "_hygCtx") "_hyg") 31)
                  (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_6]) (Lean.Expr.bvar 1))
                  (Lean.Expr.forallE
                    (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2108817691) "_hygCtx") "_hyg") 34)
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Algebra [Lean.Level.param `u_3, Lean.Level.param `u_5])
                            (Lean.Expr.bvar 8))
                          (Lean.Expr.bvar 3))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                            (Lean.Expr.bvar 8))
                          (Lean.Expr.bvar 6)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_5])
                          (Lean.Expr.bvar 3))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_5])
                            (Lean.Expr.bvar 3))
                          (Lean.Expr.bvar 1))))
                    (Lean.Expr.forallE
                      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2108817691) "_hygCtx") "_hyg") 38)
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Algebra [Lean.Level.param `u_4, Lean.Level.param `u_6])
                              (Lean.Expr.bvar 8))
                            (Lean.Expr.bvar 3))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                              (Lean.Expr.bvar 8))
                            (Lean.Expr.bvar 6)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_6])
                            (Lean.Expr.bvar 3))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_6])
                              (Lean.Expr.bvar 3))
                            (Lean.Expr.bvar 1))))
                      (Lean.Expr.forallE
                        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2108817691) "_hygCtx") "_hyg") 42)
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Algebra [Lean.Level.param `u_5, Lean.Level.param `u_6])
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.bvar 4))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_5])
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.bvar 3)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_6])
                              (Lean.Expr.bvar 4))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_6])
                                (Lean.Expr.bvar 4))
                              (Lean.Expr.bvar 2))))
                        (Lean.Expr.forallE
                          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2108817691) "_hygCtx") "_hyg") 46)
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Algebra [Lean.Level.param `u_3, Lean.Level.param `u_6])
                                  (Lean.Expr.bvar 11))
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                  (Lean.Expr.bvar 11))
                                (Lean.Expr.bvar 9)))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_6])
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_6])
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.bvar 3))))
                          (Lean.Expr.forallE
                            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2108817691) "_hygCtx") "_hyg") 50)
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `IsScalarTower
                                          [Lean.Level.param `u_3, Lean.Level.param `u_5, Lean.Level.param `u_6])
                                        (Lean.Expr.bvar 12))
                                      (Lean.Expr.bvar 7))
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `Algebra.toSMul
                                              [Lean.Level.param `u_3, Lean.Level.param `u_5])
                                            (Lean.Expr.bvar 12))
                                          (Lean.Expr.bvar 7))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                            (Lean.Expr.bvar 12))
                                          (Lean.Expr.bvar 10)))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_5])
                                          (Lean.Expr.bvar 7))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_5])
                                            (Lean.Expr.bvar 7))
                                          (Lean.Expr.bvar 5))))
                                    (Lean.Expr.bvar 3)))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `Algebra.toSMul
                                            [Lean.Level.param `u_5, Lean.Level.param `u_6])
                                          (Lean.Expr.bvar 7))
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_5])
                                          (Lean.Expr.bvar 7))
                                        (Lean.Expr.bvar 5)))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_6])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_6])
                                          (Lean.Expr.bvar 6))
                                        (Lean.Expr.bvar 4))))
                                  (Lean.Expr.bvar 1)))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Algebra.toSMul [Lean.Level.param `u_3, Lean.Level.param `u_6])
                                        (Lean.Expr.bvar 12))
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                        (Lean.Expr.bvar 12))
                                      (Lean.Expr.bvar 10)))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_6])
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_6])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 4))))
                                (Lean.Expr.bvar 0)))
                            (Lean.Expr.forallE
                              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2108817691) "_hygCtx") "_hyg") 55)
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `IsScalarTower
                                            [Lean.Level.param `u_3, Lean.Level.param `u_4, Lean.Level.param `u_6])
                                          (Lean.Expr.bvar 13))
                                        (Lean.Expr.bvar 12))
                                      (Lean.Expr.bvar 7))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `Algebra.toSMul
                                                [Lean.Level.param `u_3, Lean.Level.param `u_4])
                                              (Lean.Expr.bvar 13))
                                            (Lean.Expr.bvar 12))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                              (Lean.Expr.bvar 13))
                                            (Lean.Expr.bvar 11)))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                                            (Lean.Expr.bvar 12))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                                              (Lean.Expr.bvar 12))
                                            (Lean.Expr.bvar 10))))
                                      (Lean.Expr.bvar 9)))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `Algebra.toSMul
                                              [Lean.Level.param `u_4, Lean.Level.param `u_6])
                                            (Lean.Expr.bvar 12))
                                          (Lean.Expr.bvar 7))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                                            (Lean.Expr.bvar 12))
                                          (Lean.Expr.bvar 10)))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_6])
                                          (Lean.Expr.bvar 7))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_6])
                                            (Lean.Expr.bvar 7))
                                          (Lean.Expr.bvar 5))))
                                    (Lean.Expr.bvar 3)))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `Algebra.toSMul
                                            [Lean.Level.param `u_3, Lean.Level.param `u_6])
                                          (Lean.Expr.bvar 13))
                                        (Lean.Expr.bvar 7))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                          (Lean.Expr.bvar 13))
                                        (Lean.Expr.bvar 11)))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_6])
                                        (Lean.Expr.bvar 7))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_6])
                                          (Lean.Expr.bvar 7))
                                        (Lean.Expr.bvar 5))))
                                  (Lean.Expr.bvar 1)))
                              (Lean.Expr.forallE
                                (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2108817691) "_hygCtx") "_hyg") 60)
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `Algebra.IsPushout
                                                                [Lean.Level.param `u_4,
                                                                 Lean.Level.param `u_3,
                                                                 Lean.Level.param `u_5,
                                                                 Lean.Level.param `u_6])
                                                              (Lean.Expr.bvar 14))
                                                            (Lean.Expr.bvar 13))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `CommRing.toCommSemiring
                                                                [Lean.Level.param `u_3])
                                                              (Lean.Expr.bvar 14))
                                                            (Lean.Expr.bvar 12)))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `CommRing.toCommSemiring
                                                              [Lean.Level.param `u_4])
                                                            (Lean.Expr.bvar 13))
                                                          (Lean.Expr.bvar 11)))
                                                      (Lean.Expr.bvar 10))
                                                    (Lean.Expr.bvar 9))
                                                  (Lean.Expr.bvar 8))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_5])
                                                    (Lean.Expr.bvar 9))
                                                  (Lean.Expr.bvar 7)))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_6])
                                                  (Lean.Expr.bvar 8))
                                                (Lean.Expr.bvar 6)))
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.bvar 4))
                                        (Lean.Expr.bvar 3))
                                      (Lean.Expr.bvar 2))
                                    (Lean.Expr.bvar 1))
                                  (Lean.Expr.bvar 0))
                                (Lean.Expr.forallE
                                  (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2108817691) "_hygCtx") "_hyg") 66)
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `Module.Flat
                                              [Lean.Level.param `u_3, Lean.Level.param `u_4])
                                            (Lean.Expr.bvar 15))
                                          (Lean.Expr.bvar 14))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                            (Lean.Expr.bvar 15))
                                          (Lean.Expr.bvar 13)))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_4])
                                          (Lean.Expr.bvar 14))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                                            (Lean.Expr.bvar 14))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                                              (Lean.Expr.bvar 14))
                                            (Lean.Expr.bvar 12)))))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `Algebra.toModule
                                                [Lean.Level.param `u_3, Lean.Level.param `u_4])
                                              (Lean.Expr.bvar 15))
                                            (Lean.Expr.bvar 14))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                              (Lean.Expr.bvar 15))
                                            (Lean.Expr.bvar 13)))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                                            (Lean.Expr.bvar 14))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                                              (Lean.Expr.bvar 14))
                                            (Lean.Expr.bvar 12))))
                                      (Lean.Expr.bvar 11)))
                                  (Lean.Expr.forallE
                                    (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2108817691) "_hygCtx") "_hyg") 70)
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `Module.Finite
                                                [Lean.Level.param `u_3, Lean.Level.param `u_4])
                                              (Lean.Expr.bvar 16))
                                            (Lean.Expr.bvar 15))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_3])
                                              (Lean.Expr.bvar 16))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                                (Lean.Expr.bvar 16))
                                              (Lean.Expr.bvar 14))))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_4])
                                            (Lean.Expr.bvar 15))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                                              (Lean.Expr.bvar 15))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                                                (Lean.Expr.bvar 15))
                                              (Lean.Expr.bvar 13)))))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `Algebra.toModule
                                                  [Lean.Level.param `u_3, Lean.Level.param `u_4])
                                                (Lean.Expr.bvar 16))
                                              (Lean.Expr.bvar 15))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                                (Lean.Expr.bvar 16))
                                              (Lean.Expr.bvar 14)))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                                              (Lean.Expr.bvar 15))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                                                (Lean.Expr.bvar 15))
                                              (Lean.Expr.bvar 13))))
                                        (Lean.Expr.bvar 12)))
                                    (Lean.Expr.forallE
                                      `x
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_5])
                                          (Lean.Expr.bvar 12))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_5])
                                            (Lean.Expr.bvar 12))
                                          (Lean.Expr.bvar 10)))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                                            (Lean.Expr.const `Nat []))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `Module.rankAtStalk
                                                        [Lean.Level.param `u_5, Lean.Level.param `u_6])
                                                      (Lean.Expr.bvar 13))
                                                    (Lean.Expr.bvar 12))
                                                  (Lean.Expr.bvar 11))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `Ring.toAddCommGroup [Lean.Level.param `u_6])
                                                    (Lean.Expr.bvar 12))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `CommRing.toRing [Lean.Level.param `u_6])
                                                      (Lean.Expr.bvar 12))
                                                    (Lean.Expr.bvar 10))))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `Algebra.toModule
                                                          [Lean.Level.param `u_5, Lean.Level.param `u_6])
                                                        (Lean.Expr.bvar 13))
                                                      (Lean.Expr.bvar 12))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CommRing.toCommSemiring
                                                          [Lean.Level.param `u_5])
                                                        (Lean.Expr.bvar 13))
                                                      (Lean.Expr.bvar 11)))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_6])
                                                      (Lean.Expr.bvar 12))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CommRing.toCommSemiring
                                                          [Lean.Level.param `u_6])
                                                        (Lean.Expr.bvar 12))
                                                      (Lean.Expr.bvar 10))))
                                                (Lean.Expr.bvar 7)))
                                            (Lean.Expr.bvar 0)))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `Module.rankAtStalk
                                                      [Lean.Level.param `u_3, Lean.Level.param `u_4])
                                                    (Lean.Expr.bvar 18))
                                                  (Lean.Expr.bvar 17))
                                                (Lean.Expr.bvar 16))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `Ring.toAddCommGroup [Lean.Level.param `u_4])
                                                  (Lean.Expr.bvar 17))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `CommRing.toRing [Lean.Level.param `u_4])
                                                    (Lean.Expr.bvar 17))
                                                  (Lean.Expr.bvar 15))))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `Algebra.toModule
                                                        [Lean.Level.param `u_3, Lean.Level.param `u_4])
                                                      (Lean.Expr.bvar 18))
                                                    (Lean.Expr.bvar 17))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                                      (Lean.Expr.bvar 18))
                                                    (Lean.Expr.bvar 16)))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                                                    (Lean.Expr.bvar 17))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                                                      (Lean.Expr.bvar 17))
                                                    (Lean.Expr.bvar 15))))
                                              (Lean.Expr.bvar 14)))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `PrimeSpectrum.comap
                                                        [Lean.Level.param `u_3, Lean.Level.param `u_5])
                                                      (Lean.Expr.bvar 18))
                                                    (Lean.Expr.bvar 13))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                                      (Lean.Expr.bvar 18))
                                                    (Lean.Expr.bvar 16)))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_5])
                                                    (Lean.Expr.bvar 13))
                                                  (Lean.Expr.bvar 11)))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `Algebra.algebraMap
                                                          [Lean.Level.param `u_3, Lean.Level.param `u_5])
                                                        (Lean.Expr.bvar 18))
                                                      (Lean.Expr.bvar 13))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CommRing.toCommSemiring
                                                          [Lean.Level.param `u_3])
                                                        (Lean.Expr.bvar 18))
                                                      (Lean.Expr.bvar 16)))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_5])
                                                      (Lean.Expr.bvar 13))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CommRing.toCommSemiring
                                                          [Lean.Level.param `u_5])
                                                        (Lean.Expr.bvar 13))
                                                      (Lean.Expr.bvar 11))))
                                                (Lean.Expr.bvar 9)))
                                            (Lean.Expr.bvar 0))))
                                      (Lean.BinderInfo.default))
                                    (Lean.BinderInfo.instImplicit))
                                  (Lean.BinderInfo.instImplicit))
                                (Lean.BinderInfo.instImplicit))
                              (Lean.BinderInfo.instImplicit))
                            (Lean.BinderInfo.instImplicit))
                          (Lean.BinderInfo.instImplicit))
                        (Lean.BinderInfo.instImplicit))
                      (Lean.BinderInfo.instImplicit))
                    (Lean.BinderInfo.instImplicit))
                  (Lean.BinderInfo.instImplicit))
                (Lean.BinderInfo.instImplicit))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))),
  (`AlgebraicGeometry.Scheme.Hom.finrank, (Lean.Expr.forallE
  `X
  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
  (Lean.Expr.forallE
    `S
    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
    (Lean.Expr.forallE
      `f
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
              (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const
                  `CategoryTheory.CategoryStruct.toQuiver
                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const
                    `CategoryTheory.Category.toCategoryStruct
                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
          (Lean.Expr.bvar 1))
        (Lean.Expr.bvar 0))
      (Lean.Expr.forallE
        `s
        (Lean.Expr.app
          (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const
                  `AlgebraicGeometry.PresheafedSpace.carrier
                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const
                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                    [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
              (Lean.Expr.app
                (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace [Lean.Level.param `u])
                (Lean.Expr.app
                  (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                  (Lean.Expr.bvar 1))))))
        (Lean.Expr.const `Nat [])
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`AlgebraicGeometry.Scheme.Hom.finrank_SpecMap_algebraMap, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 3715848533) "_hygCtx") "_hyg") 13)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 3715848533) "_hygCtx") "_hyg") 16)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 3715848533) "_hygCtx") "_hyg") 19)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Algebra [Lean.Level.param `u, Lean.Level.param `u]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 3715848533) "_hygCtx") "_hyg") 23)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Module.Finite [Lean.Level.param `u, Lean.Level.param `u])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2))))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u, Lean.Level.param `u])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2)))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.forallE
              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 3715848533) "_hygCtx") "_hyg") 27)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Module.Flat [Lean.Level.param `u, Lean.Level.param `u])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 3)))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2)))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u, Lean.Level.param `u])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2))))
                  (Lean.Expr.bvar 1)))
              (Lean.Expr.forallE
                `x
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u]) (Lean.Expr.bvar 6))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 6))
                    (Lean.Expr.bvar 4)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.finrank [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.const `AlgebraicGeometry.Spec [Lean.Level.param `u])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRingCat.of [Lean.Level.param `u])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 4))))
                          (Lean.Expr.app
                            (Lean.Expr.const `AlgebraicGeometry.Spec [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `CommRingCat.of [Lean.Level.param `u]) (Lean.Expr.bvar 7))
                              (Lean.Expr.bvar 5))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `AlgebraicGeometry.Spec.map [Lean.Level.param `u])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRingCat.of [Lean.Level.param `u])
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.bvar 5)))
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `CommRingCat.of [Lean.Level.param `u]) (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 4)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRingCat.ofHom [Lean.Level.param `u])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.bvar 4))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Algebra.algebraMap [Lean.Level.param `u, Lean.Level.param `u])
                                      (Lean.Expr.bvar 7))
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                      (Lean.Expr.bvar 7))
                                    (Lean.Expr.bvar 5)))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.bvar 4))))
                              (Lean.Expr.bvar 3)))))
                      (Lean.Expr.bvar 0)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Module.rankAtStalk [Lean.Level.param `u, Lean.Level.param `u])
                              (Lean.Expr.bvar 7))
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Ring.toAddCommGroup [Lean.Level.param `u])
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `CommRing.toRing [Lean.Level.param `u]) (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 4))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u, Lean.Level.param `u])
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.bvar 5)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 4))))
                        (Lean.Expr.bvar 3)))
                    (Lean.Expr.bvar 0)))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.instImplicit))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))),
  (`AlgebraicGeometry.Scheme.Hom.finrank_SpecMap_eq_finrank, (Lean.Expr.forallE
  `R
  (Lean.Expr.const `CommRingCat [Lean.Level.param `u])
  (Lean.Expr.forallE
    `S
    (Lean.Expr.const `CommRingCat [Lean.Level.param `u])
    (Lean.Expr.forallE
      `f
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const
                  `CategoryTheory.CategoryStruct.toQuiver
                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const
                    `CategoryTheory.Category.toCategoryStruct
                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))))
          (Lean.Expr.bvar 1))
        (Lean.Expr.bvar 0))
      (Lean.Expr.forallE
        `hf₁
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `RingHom.Finite [Lean.Level.param `u, Lean.Level.param `u])
                  (Lean.Expr.app (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u]) (Lean.Expr.bvar 2)))
                (Lean.Expr.app (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u]) (Lean.Expr.bvar 1)))
              (Lean.Expr.app
                (Lean.Expr.const `CommRingCat.instCommRingObjForgetRingHomCarrier [Lean.Level.param `u])
                (Lean.Expr.bvar 2)))
            (Lean.Expr.app
              (Lean.Expr.const `CommRingCat.instCommRingObjForgetRingHomCarrier [Lean.Level.param `u])
              (Lean.Expr.bvar 1)))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommRingCat.Hom.hom [Lean.Level.param `u]) (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 1))
            (Lean.Expr.bvar 0)))
        (Lean.Expr.forallE
          `hf₂
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `RingHom.Flat [Lean.Level.param `u, Lean.Level.param `u])
                    (Lean.Expr.app (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u]) (Lean.Expr.bvar 3)))
                  (Lean.Expr.app (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u]) (Lean.Expr.bvar 2)))
                (Lean.Expr.app
                  (Lean.Expr.const `CommRingCat.instCommRingObjForgetRingHomCarrier [Lean.Level.param `u])
                  (Lean.Expr.bvar 3)))
              (Lean.Expr.app
                (Lean.Expr.const `CommRingCat.instCommRingObjForgetRingHomCarrier [Lean.Level.param `u])
                (Lean.Expr.bvar 2)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRingCat.Hom.hom [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 1)))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.param `u)])
                (Lean.Expr.forallE
                  `s
                  (Lean.Expr.app
                    (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `AlgebraicGeometry.PresheafedSpace.carrier
                            [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                              [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                        (Lean.Expr.app
                          (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace [Lean.Level.param `u])
                          (Lean.Expr.app
                            (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.const `AlgebraicGeometry.Spec [Lean.Level.param `u])
                              (Lean.Expr.bvar 4)))))))
                  (Lean.Expr.const `Nat [])
                  (Lean.BinderInfo.default)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.finrank [Lean.Level.param `u])
                    (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.Spec [Lean.Level.param `u]) (Lean.Expr.bvar 3)))
                  (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.Spec [Lean.Level.param `u]) (Lean.Expr.bvar 4)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `AlgebraicGeometry.Spec.map [Lean.Level.param `u])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.bvar 2))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `RingHom.finrank [Lean.Level.param `u, Lean.Level.param `u])
                      (Lean.Expr.app (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u]) (Lean.Expr.bvar 4)))
                    (Lean.Expr.app (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u]) (Lean.Expr.bvar 3)))
                  (Lean.Expr.app
                    (Lean.Expr.const `CommRingCat.instCommRingObjForgetRingHomCarrier [Lean.Level.param `u])
                    (Lean.Expr.bvar 4)))
                (Lean.Expr.app
                  (Lean.Expr.const `CommRingCat.instCommRingObjForgetRingHomCarrier [Lean.Level.param `u])
                  (Lean.Expr.bvar 3)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `CommRingCat.Hom.hom [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.implicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`AlgebraicGeometry.Scheme.Hom.finrank_comp_left_of_isIso, (Lean.Expr.forallE
  `X
  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
  (Lean.Expr.forallE
    `S
    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
    (Lean.Expr.forallE
      `Y
      (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
      (Lean.Expr.forallE
        `f
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const
                    `CategoryTheory.CategoryStruct.toQuiver
                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const
                      `CategoryTheory.Category.toCategoryStruct
                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                  (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
            (Lean.Expr.bvar 2))
          (Lean.Expr.bvar 0))
        (Lean.Expr.forallE
          `g
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const
                      `CategoryTheory.CategoryStruct.toQuiver
                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `CategoryTheory.Category.toCategoryStruct
                        [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                      (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                    (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
              (Lean.Expr.bvar 1))
            (Lean.Expr.bvar 2))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 1828789207) "_hygCtx") "_hyg") 32)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `CategoryTheory.IsIso
                        [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                      (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                    (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))
                  (Lean.Expr.bvar 4))
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 1))
            (Lean.Expr.forallE
              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 1828789207) "_hygCtx") "_hyg") 35)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.Flat [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                  (Lean.Expr.bvar 4))
                (Lean.Expr.bvar 1))
              (Lean.Expr.forallE
                (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 1828789207) "_hygCtx") "_hyg") 38)
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `AlgebraicGeometry.IsFinite [Lean.Level.param `u])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 5))
                  (Lean.Expr.bvar 2))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.param `u)])
                      (Lean.Expr.forallE
                        `s
                        (Lean.Expr.app
                          (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                    [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                  [Lean.Level.param `u])
                                (Lean.Expr.app
                                  (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                  (Lean.Expr.bvar 6))))))
                        (Lean.Expr.const `Nat [])
                        (Lean.BinderInfo.default)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.finrank [Lean.Level.param `u])
                          (Lean.Expr.bvar 7))
                        (Lean.Expr.bvar 6))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `CategoryTheory.CategoryStruct.comp
                                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                                    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `CategoryTheory.Category.toCategoryStruct
                                        [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                                      (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                                    (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u])))
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 3))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.finrank [Lean.Level.param `u])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 6))
                    (Lean.Expr.bvar 3)))
                (Lean.BinderInfo.instImplicit))
              (Lean.BinderInfo.instImplicit))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.implicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`AlgebraicGeometry.Scheme.Hom.finrank_eq_one_of_isIso, (Lean.Expr.forallE
  `X
  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
  (Lean.Expr.forallE
    `Y
    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
    (Lean.Expr.forallE
      `f
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
              (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const
                  `CategoryTheory.CategoryStruct.toQuiver
                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const
                    `CategoryTheory.Category.toCategoryStruct
                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
          (Lean.Expr.bvar 1))
        (Lean.Expr.bvar 0))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 2213001845) "_hygCtx") "_hyg") 27)
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `CategoryTheory.IsIso [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))
              (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 1))
          (Lean.Expr.bvar 0))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.param `u)])
              (Lean.Expr.forallE
                `s
                (Lean.Expr.app
                  (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const
                          `AlgebraicGeometry.PresheafedSpace.carrier
                          [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                      (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                            [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                      (Lean.Expr.app
                        (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace [Lean.Level.param `u])
                        (Lean.Expr.app
                          (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                          (Lean.Expr.bvar 2))))))
                (Lean.Expr.const `Nat [])
                (Lean.BinderInfo.default)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.finrank [Lean.Level.param `u])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 1)))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `OfNat.ofNat [Lean.Level.param `u])
                (Lean.Expr.forallE
                  `s
                  (Lean.Expr.app
                    (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `AlgebraicGeometry.PresheafedSpace.carrier
                            [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                              [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                        (Lean.Expr.app
                          (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace [Lean.Level.param `u])
                          (Lean.Expr.app
                            (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                            (Lean.Expr.bvar 2))))))
                  (Lean.Expr.const `Nat [])
                  (Lean.BinderInfo.default)))
              (Lean.Expr.lit (Lean.Literal.natVal 1)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `One.toOfNat1 [Lean.Level.param `u])
                (Lean.Expr.forallE
                  `s
                  (Lean.Expr.app
                    (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `AlgebraicGeometry.PresheafedSpace.carrier
                            [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                              [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                        (Lean.Expr.app
                          (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace [Lean.Level.param `u])
                          (Lean.Expr.app
                            (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                            (Lean.Expr.bvar 2))))))
                  (Lean.Expr.const `Nat [])
                  (Lean.BinderInfo.default)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Pi.instOne [Lean.Level.param `u, Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `AlgebraicGeometry.PresheafedSpace.carrier
                              [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                            (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                          (Lean.Expr.app
                            (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                              (Lean.Expr.bvar 2)))))))
                  (Lean.Expr.lam
                    `s
                    (Lean.Expr.app
                      (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `AlgebraicGeometry.PresheafedSpace.carrier
                              [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                            (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                          (Lean.Expr.app
                            (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                              (Lean.Expr.bvar 2))))))
                    (Lean.Expr.const `Nat [])
                    (Lean.BinderInfo.default)))
                (Lean.Expr.lam
                  `i
                  (Lean.Expr.app
                    (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `AlgebraicGeometry.PresheafedSpace.carrier
                            [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                              [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                        (Lean.Expr.app
                          (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace [Lean.Level.param `u])
                          (Lean.Expr.app
                            (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                            (Lean.Expr.bvar 2))))))
                  (Lean.Expr.const `Nat.instOne [])
                  (Lean.BinderInfo.default))))))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`AlgebraicGeometry.Scheme.Hom.finrank_of_isPullback, (Lean.Expr.forallE
  `P
  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
  (Lean.Expr.forallE
    `X
    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
    (Lean.Expr.forallE
      `Y
      (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
      (Lean.Expr.forallE
        `Z
        (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
        (Lean.Expr.forallE
          `fst
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const
                      `CategoryTheory.CategoryStruct.toQuiver
                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `CategoryTheory.Category.toCategoryStruct
                        [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                      (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                    (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
              (Lean.Expr.bvar 3))
            (Lean.Expr.bvar 2))
          (Lean.Expr.forallE
            `snd
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `CategoryTheory.CategoryStruct.toQuiver
                        [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                      (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const
                          `CategoryTheory.Category.toCategoryStruct
                          [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                        (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                      (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
                (Lean.Expr.bvar 4))
              (Lean.Expr.bvar 2))
            (Lean.Expr.forallE
              `f
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                      (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const
                          `CategoryTheory.CategoryStruct.toQuiver
                          [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                        (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `CategoryTheory.Category.toCategoryStruct
                            [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                          (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                        (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
                  (Lean.Expr.bvar 4))
                (Lean.Expr.bvar 2))
              (Lean.Expr.forallE
                `g
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                        (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `CategoryTheory.CategoryStruct.toQuiver
                            [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                          (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `CategoryTheory.Category.toCategoryStruct
                              [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                            (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                          (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
                    (Lean.Expr.bvar 4))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.forallE
                  `h
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `CategoryTheory.IsPullback
                                        [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                                      (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                                    (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.bvar 4))
                          (Lean.Expr.bvar 3))
                        (Lean.Expr.bvar 2))
                      (Lean.Expr.bvar 1))
                    (Lean.Expr.bvar 0))
                  (Lean.Expr.forallE
                    (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 1125782303) "_hygCtx") "_hyg") 51)
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `AlgebraicGeometry.Flat [Lean.Level.param `u])
                          (Lean.Expr.bvar 7))
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 2))
                    (Lean.Expr.forallE
                      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 1125782303) "_hygCtx") "_hyg") 54)
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `AlgebraicGeometry.IsFinite [Lean.Level.param `u])
                            (Lean.Expr.bvar 8))
                          (Lean.Expr.bvar 6))
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.forallE
                        `y
                        (Lean.Expr.app
                          (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                    [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                  [Lean.Level.param `u])
                                (Lean.Expr.app
                                  (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                  (Lean.Expr.bvar 8))))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                              (Lean.Expr.const `Nat []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.finrank [Lean.Level.param `u])
                                    (Lean.Expr.bvar 11))
                                  (Lean.Expr.bvar 9))
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 0)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.finrank [Lean.Level.param `u])
                                  (Lean.Expr.bvar 10))
                                (Lean.Expr.bvar 8))
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `DFunLike.coe
                                          [Lean.Level.succ (Lean.Level.param `u),
                                           Lean.Level.succ (Lean.Level.param `u),
                                           Lean.Level.succ (Lean.Level.param `u)])
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.lam
                                              `X
                                              (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                              (Lean.Expr.lam
                                                `Y
                                                (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `ContinuousMap
                                                          [Lean.Level.param `u, Lean.Level.param `u])
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                          (Lean.Expr.bvar 1)))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                        (Lean.Expr.bvar 0)))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                      (Lean.Expr.bvar 1)))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                    (Lean.Expr.bvar 0)))
                                                (Lean.BinderInfo.default))
                                              (Lean.BinderInfo.default))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                                    [Lean.Level.param `u,
                                                     Lean.Level.succ (Lean.Level.param `u),
                                                     Lean.Level.param `u])
                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                       Lean.Level.param `u,
                                                       Lean.Level.param `u])
                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                    [Lean.Level.param `u])
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                      [Lean.Level.param `u])
                                                    (Lean.Expr.bvar 9))))))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                                  [Lean.Level.param `u,
                                                   Lean.Level.succ (Lean.Level.param `u),
                                                   Lean.Level.param `u])
                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                     Lean.Level.param `u,
                                                     Lean.Level.param `u])
                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                  [Lean.Level.param `u])
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                    [Lean.Level.param `u])
                                                  (Lean.Expr.bvar 8)))))))
                                      (Lean.Expr.app
                                        (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `AlgebraicGeometry.PresheafedSpace.carrier
                                                [Lean.Level.param `u,
                                                 Lean.Level.succ (Lean.Level.param `u),
                                                 Lean.Level.param `u])
                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                            (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                   Lean.Level.param `u,
                                                   Lean.Level.param `u])
                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                [Lean.Level.param `u])
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                  [Lean.Level.param `u])
                                                (Lean.Expr.bvar 9)))))))
                                    (Lean.Expr.lam
                                      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                                      (Lean.Expr.app
                                        (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `AlgebraicGeometry.PresheafedSpace.carrier
                                                [Lean.Level.param `u,
                                                 Lean.Level.succ (Lean.Level.param `u),
                                                 Lean.Level.param `u])
                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                            (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                   Lean.Level.param `u,
                                                   Lean.Level.param `u])
                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                [Lean.Level.param `u])
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                  [Lean.Level.param `u])
                                                (Lean.Expr.bvar 9))))))
                                      (Lean.Expr.app
                                        (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `AlgebraicGeometry.PresheafedSpace.carrier
                                                [Lean.Level.param `u,
                                                 Lean.Level.succ (Lean.Level.param `u),
                                                 Lean.Level.param `u])
                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                            (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                   Lean.Level.param `u,
                                                   Lean.Level.param `u])
                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                [Lean.Level.param `u])
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                  [Lean.Level.param `u])
                                                (Lean.Expr.bvar 9))))))
                                      (Lean.BinderInfo.default)))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.lam
                                        `X
                                        (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                        (Lean.Expr.lam
                                          `Y
                                          (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `ContinuousMap.instFunLike
                                                    [Lean.Level.param `u, Lean.Level.param `u])
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                    (Lean.Expr.bvar 1)))
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                  (Lean.Expr.bvar 0)))
                                              (Lean.Expr.app
                                                (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                (Lean.Expr.bvar 1)))
                                            (Lean.Expr.app
                                              (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                              (Lean.Expr.bvar 0)))
                                          (Lean.BinderInfo.default))
                                        (Lean.BinderInfo.default))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.PresheafedSpace.carrier
                                              [Lean.Level.param `u,
                                               Lean.Level.succ (Lean.Level.param `u),
                                               Lean.Level.param `u])
                                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                [Lean.Level.succ (Lean.Level.param `u),
                                                 Lean.Level.param `u,
                                                 Lean.Level.param `u])
                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                            (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                              [Lean.Level.param `u])
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                [Lean.Level.param `u])
                                              (Lean.Expr.bvar 9))))))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.PresheafedSpace.carrier
                                            [Lean.Level.param `u,
                                             Lean.Level.succ (Lean.Level.param `u),
                                             Lean.Level.param `u])
                                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                              [Lean.Level.succ (Lean.Level.param `u),
                                               Lean.Level.param `u,
                                               Lean.Level.param `u])
                                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                            [Lean.Level.param `u])
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                              [Lean.Level.param `u])
                                            (Lean.Expr.bvar 8)))))))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `CategoryTheory.ConcreteCategory.hom
                                                    [Lean.Level.param `u,
                                                     Lean.Level.param `u,
                                                     Lean.Level.succ (Lean.Level.param `u),
                                                     Lean.Level.param `u])
                                                  (Lean.Expr.const `TopCat [Lean.Level.param `u]))
                                                (Lean.Expr.const `TopCat.instCategory [Lean.Level.param `u]))
                                              (Lean.Expr.lam
                                                `X
                                                (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                                (Lean.Expr.lam
                                                  `Y
                                                  (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `ContinuousMap
                                                            [Lean.Level.param `u, Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                            (Lean.Expr.bvar 1)))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                          (Lean.Expr.bvar 0)))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                        (Lean.Expr.bvar 1)))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                      (Lean.Expr.bvar 0)))
                                                  (Lean.BinderInfo.default))
                                                (Lean.BinderInfo.default)))
                                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u]))
                                          (Lean.Expr.lam
                                            `X
                                            (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                            (Lean.Expr.lam
                                              `Y
                                              (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `ContinuousMap.instFunLike
                                                        [Lean.Level.param `u, Lean.Level.param `u])
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                        (Lean.Expr.bvar 1)))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                      (Lean.Expr.bvar 0)))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                    (Lean.Expr.bvar 1)))
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                  (Lean.Expr.bvar 0)))
                                              (Lean.BinderInfo.default))
                                            (Lean.BinderInfo.default)))
                                        (Lean.Expr.const
                                          `TopCat.instConcreteCategoryContinuousMapCarrier
                                          [Lean.Level.param `u]))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.PresheafedSpace.carrier
                                              [Lean.Level.param `u,
                                               Lean.Level.succ (Lean.Level.param `u),
                                               Lean.Level.param `u])
                                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                [Lean.Level.succ (Lean.Level.param `u),
                                                 Lean.Level.param `u,
                                                 Lean.Level.param `u])
                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                            (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                              [Lean.Level.param `u])
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                [Lean.Level.param `u])
                                              (Lean.Expr.bvar 9))))))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.PresheafedSpace.carrier
                                            [Lean.Level.param `u,
                                             Lean.Level.succ (Lean.Level.param `u),
                                             Lean.Level.param `u])
                                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                              [Lean.Level.succ (Lean.Level.param `u),
                                               Lean.Level.param `u,
                                               Lean.Level.param `u])
                                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                            [Lean.Level.param `u])
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                              [Lean.Level.param `u])
                                            (Lean.Expr.bvar 8))))))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.PresheafedSpace.Hom.base
                                              [Lean.Level.param `u,
                                               Lean.Level.succ (Lean.Level.param `u),
                                               Lean.Level.param `u])
                                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                [Lean.Level.succ (Lean.Level.param `u),
                                                 Lean.Level.param `u,
                                                 Lean.Level.param `u])
                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                            (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                              [Lean.Level.param `u])
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                [Lean.Level.param `u])
                                              (Lean.Expr.bvar 9)))))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                              [Lean.Level.succ (Lean.Level.param `u),
                                               Lean.Level.param `u,
                                               Lean.Level.param `u])
                                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                            [Lean.Level.param `u])
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                              [Lean.Level.param `u])
                                            (Lean.Expr.bvar 8)))))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.LocallyRingedSpace.Hom.toHom
                                            [Lean.Level.param `u])
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                              [Lean.Level.param `u])
                                            (Lean.Expr.bvar 9)))
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                            [Lean.Level.param `u])
                                          (Lean.Expr.bvar 8)))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.Scheme.Hom.toLRSHom'
                                              [Lean.Level.param `u])
                                            (Lean.Expr.bvar 9))
                                          (Lean.Expr.bvar 8))
                                        (Lean.Expr.bvar 4))))))
                              (Lean.Expr.bvar 0))))
                        (Lean.BinderInfo.default))
                      (Lean.BinderInfo.instImplicit))
                    (Lean.BinderInfo.instImplicit))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.implicit))
      (Lean.BinderInfo.implicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`AlgebraicGeometry.Scheme.Hom.finrank_pullback_fst, (Lean.Expr.forallE
  `X
  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
  (Lean.Expr.forallE
    `Y
    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
    (Lean.Expr.forallE
      `Z
      (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
      (Lean.Expr.forallE
        `f
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const
                    `CategoryTheory.CategoryStruct.toQuiver
                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const
                      `CategoryTheory.Category.toCategoryStruct
                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                  (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
            (Lean.Expr.bvar 2))
          (Lean.Expr.bvar 0))
        (Lean.Expr.forallE
          `g
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const
                      `CategoryTheory.CategoryStruct.toQuiver
                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `CategoryTheory.Category.toCategoryStruct
                        [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                      (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                    (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
              (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 1))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 1938423121) "_hygCtx") "_hyg") 33)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.Flat [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 1))
            (Lean.Expr.forallE
              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 1938423121) "_hygCtx") "_hyg") 36)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.IsFinite [Lean.Level.param `u]) (Lean.Expr.bvar 5))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.forallE
                `y
                (Lean.Expr.app
                  (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const
                          `AlgebraicGeometry.PresheafedSpace.carrier
                          [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                      (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                            [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                      (Lean.Expr.app
                        (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace [Lean.Level.param `u])
                        (Lean.Expr.app
                          (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                          (Lean.Expr.bvar 5))))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.finrank [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `CategoryTheory.Limits.pullback
                                              [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                                            (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.Scheme.instCategory
                                            [Lean.Level.param `u]))
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 7))
                                    (Lean.Expr.bvar 5))
                                  (Lean.Expr.bvar 3))
                                (Lean.Expr.bvar 4))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.Scheme.Pullback.instHasPullback
                                          [Lean.Level.param `u])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 7))
                                    (Lean.Expr.bvar 5))
                                  (Lean.Expr.bvar 3))
                                (Lean.Expr.bvar 4))))
                          (Lean.Expr.bvar 6))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `CategoryTheory.Limits.pullback.fst
                                          [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                                        (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                                      (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.bvar 3))
                            (Lean.Expr.bvar 4))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.Pullback.instHasPullback
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.bvar 3))
                            (Lean.Expr.bvar 4))))
                      (Lean.Expr.bvar 0)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.finrank [Lean.Level.param `u])
                          (Lean.Expr.bvar 7))
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `DFunLike.coe
                                  [Lean.Level.succ (Lean.Level.param `u),
                                   Lean.Level.succ (Lean.Level.param `u),
                                   Lean.Level.succ (Lean.Level.param `u)])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.lam
                                      `X
                                      (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                      (Lean.Expr.lam
                                        `Y
                                        (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `ContinuousMap
                                                  [Lean.Level.param `u, Lean.Level.param `u])
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                  (Lean.Expr.bvar 1)))
                                              (Lean.Expr.app
                                                (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                (Lean.Expr.bvar 0)))
                                            (Lean.Expr.app
                                              (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                              (Lean.Expr.bvar 1)))
                                          (Lean.Expr.app
                                            (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                            (Lean.Expr.bvar 0)))
                                        (Lean.BinderInfo.default))
                                      (Lean.BinderInfo.default))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.PresheafedSpace.carrier
                                            [Lean.Level.param `u,
                                             Lean.Level.succ (Lean.Level.param `u),
                                             Lean.Level.param `u])
                                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                              [Lean.Level.succ (Lean.Level.param `u),
                                               Lean.Level.param `u,
                                               Lean.Level.param `u])
                                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                            [Lean.Level.param `u])
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                              [Lean.Level.param `u])
                                            (Lean.Expr.bvar 6))))))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.PresheafedSpace.carrier
                                          [Lean.Level.param `u,
                                           Lean.Level.succ (Lean.Level.param `u),
                                           Lean.Level.param `u])
                                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                      (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                            [Lean.Level.succ (Lean.Level.param `u),
                                             Lean.Level.param `u,
                                             Lean.Level.param `u])
                                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                          [Lean.Level.param `u])
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                            [Lean.Level.param `u])
                                          (Lean.Expr.bvar 5)))))))
                              (Lean.Expr.app
                                (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.PresheafedSpace.carrier
                                        [Lean.Level.param `u,
                                         Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                          [Lean.Level.succ (Lean.Level.param `u),
                                           Lean.Level.param `u,
                                           Lean.Level.param `u])
                                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                      (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                        [Lean.Level.param `u])
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                          [Lean.Level.param `u])
                                        (Lean.Expr.bvar 6)))))))
                            (Lean.Expr.lam
                              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                              (Lean.Expr.app
                                (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.PresheafedSpace.carrier
                                        [Lean.Level.param `u,
                                         Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                          [Lean.Level.succ (Lean.Level.param `u),
                                           Lean.Level.param `u,
                                           Lean.Level.param `u])
                                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                      (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                        [Lean.Level.param `u])
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                          [Lean.Level.param `u])
                                        (Lean.Expr.bvar 6))))))
                              (Lean.Expr.app
                                (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.PresheafedSpace.carrier
                                        [Lean.Level.param `u,
                                         Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                          [Lean.Level.succ (Lean.Level.param `u),
                                           Lean.Level.param `u,
                                           Lean.Level.param `u])
                                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                      (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                        [Lean.Level.param `u])
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                          [Lean.Level.param `u])
                                        (Lean.Expr.bvar 6))))))
                              (Lean.BinderInfo.default)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.lam
                                `X
                                (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                (Lean.Expr.lam
                                  `Y
                                  (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `ContinuousMap.instFunLike
                                            [Lean.Level.param `u, Lean.Level.param `u])
                                          (Lean.Expr.app
                                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                            (Lean.Expr.bvar 1)))
                                        (Lean.Expr.app
                                          (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                          (Lean.Expr.bvar 0)))
                                      (Lean.Expr.app
                                        (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                        (Lean.Expr.bvar 1)))
                                    (Lean.Expr.app
                                      (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                      (Lean.Expr.bvar 0)))
                                  (Lean.BinderInfo.default))
                                (Lean.BinderInfo.default))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.PresheafedSpace.carrier
                                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                        [Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u,
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                        [Lean.Level.param `u])
                                      (Lean.Expr.bvar 6))))))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                      [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                    [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 5)))))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `CategoryTheory.ConcreteCategory.hom
                                            [Lean.Level.param `u,
                                             Lean.Level.param `u,
                                             Lean.Level.succ (Lean.Level.param `u),
                                             Lean.Level.param `u])
                                          (Lean.Expr.const `TopCat [Lean.Level.param `u]))
                                        (Lean.Expr.const `TopCat.instCategory [Lean.Level.param `u]))
                                      (Lean.Expr.lam
                                        `X
                                        (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                        (Lean.Expr.lam
                                          `Y
                                          (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `ContinuousMap
                                                    [Lean.Level.param `u, Lean.Level.param `u])
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                    (Lean.Expr.bvar 1)))
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                  (Lean.Expr.bvar 0)))
                                              (Lean.Expr.app
                                                (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                (Lean.Expr.bvar 1)))
                                            (Lean.Expr.app
                                              (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                              (Lean.Expr.bvar 0)))
                                          (Lean.BinderInfo.default))
                                        (Lean.BinderInfo.default)))
                                    (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u]))
                                  (Lean.Expr.lam
                                    `X
                                    (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                    (Lean.Expr.lam
                                      `Y
                                      (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `ContinuousMap.instFunLike
                                                [Lean.Level.param `u, Lean.Level.param `u])
                                              (Lean.Expr.app
                                                (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                (Lean.Expr.bvar 1)))
                                            (Lean.Expr.app
                                              (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                              (Lean.Expr.bvar 0)))
                                          (Lean.Expr.app
                                            (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                            (Lean.Expr.bvar 1)))
                                        (Lean.Expr.app
                                          (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                          (Lean.Expr.bvar 0)))
                                      (Lean.BinderInfo.default))
                                    (Lean.BinderInfo.default)))
                                (Lean.Expr.const
                                  `TopCat.instConcreteCategoryContinuousMapCarrier
                                  [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.PresheafedSpace.carrier
                                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                        [Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u,
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                        [Lean.Level.param `u])
                                      (Lean.Expr.bvar 6))))))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                      [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                    [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 5))))))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.PresheafedSpace.Hom.base
                                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                        [Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u,
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                        [Lean.Level.param `u])
                                      (Lean.Expr.bvar 6)))))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                      [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                    [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 5)))))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.LocallyRingedSpace.Hom.toHom
                                    [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 6)))
                                (Lean.Expr.app
                                  (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                  (Lean.Expr.bvar 5)))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.toLRSHom' [Lean.Level.param `u])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.bvar 3))))))
                      (Lean.Expr.bvar 0))))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.instImplicit))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.implicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`AlgebraicGeometry.Scheme.Hom.finrank_pullback_snd, (Lean.Expr.forallE
  `X
  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
  (Lean.Expr.forallE
    `Y
    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
    (Lean.Expr.forallE
      `Z
      (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
      (Lean.Expr.forallE
        `f
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const
                    `CategoryTheory.CategoryStruct.toQuiver
                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const
                      `CategoryTheory.Category.toCategoryStruct
                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                  (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
            (Lean.Expr.bvar 2))
          (Lean.Expr.bvar 0))
        (Lean.Expr.forallE
          `g
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const
                      `CategoryTheory.CategoryStruct.toQuiver
                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `CategoryTheory.Category.toCategoryStruct
                        [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                      (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                    (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
              (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 1))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 800494336) "_hygCtx") "_hyg") 33)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.Flat [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 1))
            (Lean.Expr.forallE
              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 800494336) "_hygCtx") "_hyg") 36)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.IsFinite [Lean.Level.param `u]) (Lean.Expr.bvar 5))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.forallE
                `y
                (Lean.Expr.app
                  (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const
                          `AlgebraicGeometry.PresheafedSpace.carrier
                          [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                      (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                            [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                      (Lean.Expr.app
                        (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace [Lean.Level.param `u])
                        (Lean.Expr.app
                          (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                          (Lean.Expr.bvar 5))))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.finrank [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `CategoryTheory.Limits.pullback
                                              [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                                            (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.Scheme.instCategory
                                            [Lean.Level.param `u]))
                                        (Lean.Expr.bvar 7))
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.bvar 5))
                                  (Lean.Expr.bvar 4))
                                (Lean.Expr.bvar 3))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.Scheme.Pullback.instHasPullback
                                          [Lean.Level.param `u])
                                        (Lean.Expr.bvar 7))
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.bvar 5))
                                  (Lean.Expr.bvar 4))
                                (Lean.Expr.bvar 3))))
                          (Lean.Expr.bvar 6))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `CategoryTheory.Limits.pullback.snd
                                          [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                                        (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                                      (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.bvar 4))
                            (Lean.Expr.bvar 3))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.Pullback.instHasPullback
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.bvar 4))
                            (Lean.Expr.bvar 3))))
                      (Lean.Expr.bvar 0)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.finrank [Lean.Level.param `u])
                          (Lean.Expr.bvar 7))
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `DFunLike.coe
                                  [Lean.Level.succ (Lean.Level.param `u),
                                   Lean.Level.succ (Lean.Level.param `u),
                                   Lean.Level.succ (Lean.Level.param `u)])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.lam
                                      `X
                                      (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                      (Lean.Expr.lam
                                        `Y
                                        (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `ContinuousMap
                                                  [Lean.Level.param `u, Lean.Level.param `u])
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                  (Lean.Expr.bvar 1)))
                                              (Lean.Expr.app
                                                (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                (Lean.Expr.bvar 0)))
                                            (Lean.Expr.app
                                              (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                              (Lean.Expr.bvar 1)))
                                          (Lean.Expr.app
                                            (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                            (Lean.Expr.bvar 0)))
                                        (Lean.BinderInfo.default))
                                      (Lean.BinderInfo.default))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.PresheafedSpace.carrier
                                            [Lean.Level.param `u,
                                             Lean.Level.succ (Lean.Level.param `u),
                                             Lean.Level.param `u])
                                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                              [Lean.Level.succ (Lean.Level.param `u),
                                               Lean.Level.param `u,
                                               Lean.Level.param `u])
                                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                            [Lean.Level.param `u])
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                              [Lean.Level.param `u])
                                            (Lean.Expr.bvar 6))))))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.PresheafedSpace.carrier
                                          [Lean.Level.param `u,
                                           Lean.Level.succ (Lean.Level.param `u),
                                           Lean.Level.param `u])
                                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                      (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                            [Lean.Level.succ (Lean.Level.param `u),
                                             Lean.Level.param `u,
                                             Lean.Level.param `u])
                                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                          [Lean.Level.param `u])
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                            [Lean.Level.param `u])
                                          (Lean.Expr.bvar 5)))))))
                              (Lean.Expr.app
                                (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.PresheafedSpace.carrier
                                        [Lean.Level.param `u,
                                         Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                          [Lean.Level.succ (Lean.Level.param `u),
                                           Lean.Level.param `u,
                                           Lean.Level.param `u])
                                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                      (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                        [Lean.Level.param `u])
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                          [Lean.Level.param `u])
                                        (Lean.Expr.bvar 6)))))))
                            (Lean.Expr.lam
                              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                              (Lean.Expr.app
                                (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.PresheafedSpace.carrier
                                        [Lean.Level.param `u,
                                         Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                          [Lean.Level.succ (Lean.Level.param `u),
                                           Lean.Level.param `u,
                                           Lean.Level.param `u])
                                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                      (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                        [Lean.Level.param `u])
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                          [Lean.Level.param `u])
                                        (Lean.Expr.bvar 6))))))
                              (Lean.Expr.app
                                (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.PresheafedSpace.carrier
                                        [Lean.Level.param `u,
                                         Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                          [Lean.Level.succ (Lean.Level.param `u),
                                           Lean.Level.param `u,
                                           Lean.Level.param `u])
                                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                      (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                        [Lean.Level.param `u])
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                          [Lean.Level.param `u])
                                        (Lean.Expr.bvar 6))))))
                              (Lean.BinderInfo.default)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.lam
                                `X
                                (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                (Lean.Expr.lam
                                  `Y
                                  (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `ContinuousMap.instFunLike
                                            [Lean.Level.param `u, Lean.Level.param `u])
                                          (Lean.Expr.app
                                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                            (Lean.Expr.bvar 1)))
                                        (Lean.Expr.app
                                          (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                          (Lean.Expr.bvar 0)))
                                      (Lean.Expr.app
                                        (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                        (Lean.Expr.bvar 1)))
                                    (Lean.Expr.app
                                      (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                      (Lean.Expr.bvar 0)))
                                  (Lean.BinderInfo.default))
                                (Lean.BinderInfo.default))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.PresheafedSpace.carrier
                                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                        [Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u,
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                        [Lean.Level.param `u])
                                      (Lean.Expr.bvar 6))))))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                      [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                    [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 5)))))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `CategoryTheory.ConcreteCategory.hom
                                            [Lean.Level.param `u,
                                             Lean.Level.param `u,
                                             Lean.Level.succ (Lean.Level.param `u),
                                             Lean.Level.param `u])
                                          (Lean.Expr.const `TopCat [Lean.Level.param `u]))
                                        (Lean.Expr.const `TopCat.instCategory [Lean.Level.param `u]))
                                      (Lean.Expr.lam
                                        `X
                                        (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                        (Lean.Expr.lam
                                          `Y
                                          (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `ContinuousMap
                                                    [Lean.Level.param `u, Lean.Level.param `u])
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                    (Lean.Expr.bvar 1)))
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                  (Lean.Expr.bvar 0)))
                                              (Lean.Expr.app
                                                (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                (Lean.Expr.bvar 1)))
                                            (Lean.Expr.app
                                              (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                              (Lean.Expr.bvar 0)))
                                          (Lean.BinderInfo.default))
                                        (Lean.BinderInfo.default)))
                                    (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u]))
                                  (Lean.Expr.lam
                                    `X
                                    (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                    (Lean.Expr.lam
                                      `Y
                                      (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `ContinuousMap.instFunLike
                                                [Lean.Level.param `u, Lean.Level.param `u])
                                              (Lean.Expr.app
                                                (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                (Lean.Expr.bvar 1)))
                                            (Lean.Expr.app
                                              (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                              (Lean.Expr.bvar 0)))
                                          (Lean.Expr.app
                                            (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                            (Lean.Expr.bvar 1)))
                                        (Lean.Expr.app
                                          (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                          (Lean.Expr.bvar 0)))
                                      (Lean.BinderInfo.default))
                                    (Lean.BinderInfo.default)))
                                (Lean.Expr.const
                                  `TopCat.instConcreteCategoryContinuousMapCarrier
                                  [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.PresheafedSpace.carrier
                                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                        [Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u,
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                        [Lean.Level.param `u])
                                      (Lean.Expr.bvar 6))))))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                      [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                    [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 5))))))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.PresheafedSpace.Hom.base
                                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                        [Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u,
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                        [Lean.Level.param `u])
                                      (Lean.Expr.bvar 6)))))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                      [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                    [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 5)))))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.LocallyRingedSpace.Hom.toHom
                                    [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 6)))
                                (Lean.Expr.app
                                  (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                  (Lean.Expr.bvar 5)))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.toLRSHom' [Lean.Level.param `u])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.bvar 3))))))
                      (Lean.Expr.bvar 0))))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.instImplicit))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.implicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`AlgebraicGeometry.Scheme.Hom.isIso_iff_finrank_eq, (Lean.Expr.forallE
  `X
  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
  (Lean.Expr.forallE
    `Y
    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
    (Lean.Expr.forallE
      `f
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
              (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const
                  `CategoryTheory.CategoryStruct.toQuiver
                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const
                    `CategoryTheory.Category.toCategoryStruct
                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
          (Lean.Expr.bvar 1))
        (Lean.Expr.bvar 0))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 2935327432) "_hygCtx") "_hyg") 16)
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.Flat [Lean.Level.param `u]) (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 1))
          (Lean.Expr.bvar 0))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 2935327432) "_hygCtx") "_hyg") 19)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.IsFinite [Lean.Level.param `u]) (Lean.Expr.bvar 3))
              (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 1))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Iff [])
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const
                          `CategoryTheory.IsIso
                          [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                        (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                      (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))
                    (Lean.Expr.bvar 4))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.forallE
                    `s
                    (Lean.Expr.app
                      (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `AlgebraicGeometry.PresheafedSpace.carrier
                              [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                            (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                          (Lean.Expr.app
                            (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                              (Lean.Expr.bvar 3))))))
                    (Lean.Expr.const `Nat [])
                    (Lean.BinderInfo.default)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.finrank [Lean.Level.param `u])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.bvar 2)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `OfNat.ofNat [Lean.Level.param `u])
                    (Lean.Expr.forallE
                      `s
                      (Lean.Expr.app
                        (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `AlgebraicGeometry.PresheafedSpace.carrier
                                [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                            (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                  [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                [Lean.Level.param `u])
                              (Lean.Expr.app
                                (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                (Lean.Expr.bvar 3))))))
                      (Lean.Expr.const `Nat [])
                      (Lean.BinderInfo.default)))
                  (Lean.Expr.lit (Lean.Literal.natVal 1)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `One.toOfNat1 [Lean.Level.param `u])
                    (Lean.Expr.forallE
                      `s
                      (Lean.Expr.app
                        (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `AlgebraicGeometry.PresheafedSpace.carrier
                                [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                            (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                  [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                [Lean.Level.param `u])
                              (Lean.Expr.app
                                (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                (Lean.Expr.bvar 3))))))
                      (Lean.Expr.const `Nat [])
                      (Lean.BinderInfo.default)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Pi.instOne [Lean.Level.param `u, Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                    [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                  [Lean.Level.param `u])
                                (Lean.Expr.app
                                  (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                  (Lean.Expr.bvar 3)))))))
                      (Lean.Expr.lam
                        `s
                        (Lean.Expr.app
                          (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                    [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                  [Lean.Level.param `u])
                                (Lean.Expr.app
                                  (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                  (Lean.Expr.bvar 3))))))
                        (Lean.Expr.const `Nat [])
                        (Lean.BinderInfo.default)))
                    (Lean.Expr.lam
                      `i
                      (Lean.Expr.app
                        (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `AlgebraicGeometry.PresheafedSpace.carrier
                                [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                            (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                  [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                [Lean.Level.param `u])
                              (Lean.Expr.app
                                (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                (Lean.Expr.bvar 3))))))
                      (Lean.Expr.const `Nat.instOne [])
                      (Lean.BinderInfo.default)))))))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`AlgebraicGeometry.Scheme.Hom.isLocallyConstant_finrank, (Lean.Expr.forallE
  `X
  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
  (Lean.Expr.forallE
    `Y
    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
    (Lean.Expr.forallE
      `f
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
              (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const
                  `CategoryTheory.CategoryStruct.toQuiver
                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const
                    `CategoryTheory.Category.toCategoryStruct
                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
          (Lean.Expr.bvar 1))
        (Lean.Expr.bvar 0))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 68476225) "_hygCtx") "_hyg") 16)
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.Flat [Lean.Level.param `u]) (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 1))
          (Lean.Expr.bvar 0))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 68476225) "_hygCtx") "_hyg") 19)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.IsFinite [Lean.Level.param `u]) (Lean.Expr.bvar 3))
              (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 1))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 68476225) "_hygCtx") "_hyg") 22)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `AlgebraicGeometry.LocallyOfFinitePresentation [Lean.Level.param `u])
                  (Lean.Expr.bvar 4))
                (Lean.Expr.bvar 3))
              (Lean.Expr.bvar 2))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `IsLocallyConstant [Lean.Level.param `u, Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `AlgebraicGeometry.PresheafedSpace.carrier
                              [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                            (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                          (Lean.Expr.app
                            (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                              (Lean.Expr.bvar 4)))))))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier
                        [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                  (Lean.Expr.app
                    (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace [Lean.Level.param `u])
                    (Lean.Expr.app
                      (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                      (Lean.Expr.bvar 4)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.finrank [Lean.Level.param `u])
                    (Lean.Expr.bvar 5))
                  (Lean.Expr.bvar 4))
                (Lean.Expr.bvar 3)))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`AlgebraicGeometry.Scheme.Hom.one_le_finrank_iff_surjective, (Lean.Expr.forallE
  `X
  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
  (Lean.Expr.forallE
    `Y
    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
    (Lean.Expr.forallE
      `f
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
              (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const
                  `CategoryTheory.CategoryStruct.toQuiver
                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const
                    `CategoryTheory.Category.toCategoryStruct
                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
          (Lean.Expr.bvar 1))
        (Lean.Expr.bvar 0))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 2785836577) "_hygCtx") "_hyg") 16)
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.Flat [Lean.Level.param `u]) (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 1))
          (Lean.Expr.bvar 0))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 2785836577) "_hygCtx") "_hyg") 19)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.IsFinite [Lean.Level.param `u]) (Lean.Expr.bvar 3))
              (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 1))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Iff [])
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `LE.le [Lean.Level.param `u])
                      (Lean.Expr.forallE
                        `s
                        (Lean.Expr.app
                          (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                    [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                  [Lean.Level.param `u])
                                (Lean.Expr.app
                                  (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                  (Lean.Expr.bvar 3))))))
                        (Lean.Expr.const `Nat [])
                        (Lean.BinderInfo.default)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Pi.hasLe [Lean.Level.param `u, Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                      [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                    [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 3)))))))
                        (Lean.Expr.lam
                          `s
                          (Lean.Expr.app
                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                      [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                    [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 3))))))
                          (Lean.Expr.const `Nat [])
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.lam
                        `i
                        (Lean.Expr.app
                          (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                    [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                  [Lean.Level.param `u])
                                (Lean.Expr.app
                                  (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                  (Lean.Expr.bvar 3))))))
                        (Lean.Expr.const `instLENat [])
                        (Lean.BinderInfo.default))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `OfNat.ofNat [Lean.Level.param `u])
                        (Lean.Expr.forallE
                          `s
                          (Lean.Expr.app
                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                      [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                    [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 3))))))
                          (Lean.Expr.const `Nat [])
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.lit (Lean.Literal.natVal 1)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `One.toOfNat1 [Lean.Level.param `u])
                        (Lean.Expr.forallE
                          `s
                          (Lean.Expr.app
                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                      [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                    [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 3))))))
                          (Lean.Expr.const `Nat [])
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Pi.instOne [Lean.Level.param `u, Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.PresheafedSpace.carrier
                                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                        [Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u,
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                        [Lean.Level.param `u])
                                      (Lean.Expr.bvar 3)))))))
                          (Lean.Expr.lam
                            `s
                            (Lean.Expr.app
                              (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.PresheafedSpace.carrier
                                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                        [Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u,
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                        [Lean.Level.param `u])
                                      (Lean.Expr.bvar 3))))))
                            (Lean.Expr.const `Nat [])
                            (Lean.BinderInfo.default)))
                        (Lean.Expr.lam
                          `i
                          (Lean.Expr.app
                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                      [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                    [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 3))))))
                          (Lean.Expr.const `Nat.instOne [])
                          (Lean.BinderInfo.default))))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.finrank [Lean.Level.param `u])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.bvar 2))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.Surjective [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                (Lean.Expr.bvar 3))
              (Lean.Expr.bvar 2)))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`AlgebraicGeometry.Scheme.Hom.one_le_finrank_map, (Lean.Expr.forallE
  `X
  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
  (Lean.Expr.forallE
    `Y
    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
    (Lean.Expr.forallE
      `f
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
              (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const
                  `CategoryTheory.CategoryStruct.toQuiver
                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const
                    `CategoryTheory.Category.toCategoryStruct
                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
          (Lean.Expr.bvar 1))
        (Lean.Expr.bvar 0))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 1793465933) "_hygCtx") "_hyg") 16)
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.Flat [Lean.Level.param `u]) (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 1))
          (Lean.Expr.bvar 0))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdSchemeFlatRank 1793465933) "_hygCtx") "_hyg") 19)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.IsFinite [Lean.Level.param `u]) (Lean.Expr.bvar 3))
              (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 1))
          (Lean.Expr.forallE
            `x
            (Lean.Expr.app
              (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const
                      `AlgebraicGeometry.PresheafedSpace.carrier
                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                        [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                  (Lean.Expr.app
                    (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace [Lean.Level.param `u])
                    (Lean.Expr.app
                      (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                      (Lean.Expr.bvar 4))))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `instLENat []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.lit (Lean.Literal.natVal 1)))
                  (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.finrank [Lean.Level.param `u])
                      (Lean.Expr.bvar 5))
                    (Lean.Expr.bvar 4))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `DFunLike.coe
                              [Lean.Level.succ (Lean.Level.param `u),
                               Lean.Level.succ (Lean.Level.param `u),
                               Lean.Level.succ (Lean.Level.param `u)])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.lam
                                  `X
                                  (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                  (Lean.Expr.lam
                                    `Y
                                    (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `ContinuousMap [Lean.Level.param `u, Lean.Level.param `u])
                                            (Lean.Expr.app
                                              (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                              (Lean.Expr.bvar 1)))
                                          (Lean.Expr.app
                                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                            (Lean.Expr.bvar 0)))
                                        (Lean.Expr.app
                                          (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                          (Lean.Expr.bvar 1)))
                                      (Lean.Expr.app
                                        (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                        (Lean.Expr.bvar 0)))
                                    (Lean.BinderInfo.default))
                                  (Lean.BinderInfo.default))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.PresheafedSpace.carrier
                                        [Lean.Level.param `u,
                                         Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                          [Lean.Level.succ (Lean.Level.param `u),
                                           Lean.Level.param `u,
                                           Lean.Level.param `u])
                                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                      (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                        [Lean.Level.param `u])
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                          [Lean.Level.param `u])
                                        (Lean.Expr.bvar 5))))))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.PresheafedSpace.carrier
                                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                        [Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u,
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                        [Lean.Level.param `u])
                                      (Lean.Expr.bvar 4)))))))
                          (Lean.Expr.app
                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                      [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                    [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 5)))))))
                        (Lean.Expr.lam
                          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                          (Lean.Expr.app
                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                      [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                    [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 5))))))
                          (Lean.Expr.app
                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                    [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                      [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                  (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                    [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 5))))))
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.lam
                            `X
                            (Lean.Expr.const `TopCat [Lean.Level.param `u])
                            (Lean.Expr.lam
                              `Y
                              (Lean.Expr.const `TopCat [Lean.Level.param `u])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `ContinuousMap.instFunLike
                                        [Lean.Level.param `u, Lean.Level.param `u])
                                      (Lean.Expr.app
                                        (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                        (Lean.Expr.bvar 1)))
                                    (Lean.Expr.app
                                      (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                      (Lean.Expr.bvar 0)))
                                  (Lean.Expr.app
                                    (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                    (Lean.Expr.bvar 1)))
                                (Lean.Expr.app (Lean.Expr.const `TopCat.str [Lean.Level.param `u]) (Lean.Expr.bvar 0)))
                              (Lean.BinderInfo.default))
                            (Lean.BinderInfo.default))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                    [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                  [Lean.Level.param `u])
                                (Lean.Expr.app
                                  (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                  (Lean.Expr.bvar 5))))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `AlgebraicGeometry.PresheafedSpace.carrier
                                [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                            (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                  [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                [Lean.Level.param `u])
                              (Lean.Expr.app
                                (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                (Lean.Expr.bvar 4)))))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `CategoryTheory.ConcreteCategory.hom
                                        [Lean.Level.param `u,
                                         Lean.Level.param `u,
                                         Lean.Level.succ (Lean.Level.param `u),
                                         Lean.Level.param `u])
                                      (Lean.Expr.const `TopCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `TopCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.lam
                                    `X
                                    (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                    (Lean.Expr.lam
                                      `Y
                                      (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `ContinuousMap
                                                [Lean.Level.param `u, Lean.Level.param `u])
                                              (Lean.Expr.app
                                                (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                (Lean.Expr.bvar 1)))
                                            (Lean.Expr.app
                                              (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                              (Lean.Expr.bvar 0)))
                                          (Lean.Expr.app
                                            (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                            (Lean.Expr.bvar 1)))
                                        (Lean.Expr.app
                                          (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                          (Lean.Expr.bvar 0)))
                                      (Lean.BinderInfo.default))
                                    (Lean.BinderInfo.default)))
                                (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u]))
                              (Lean.Expr.lam
                                `X
                                (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                (Lean.Expr.lam
                                  `Y
                                  (Lean.Expr.const `TopCat [Lean.Level.param `u])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `ContinuousMap.instFunLike
                                            [Lean.Level.param `u, Lean.Level.param `u])
                                          (Lean.Expr.app
                                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                            (Lean.Expr.bvar 1)))
                                        (Lean.Expr.app
                                          (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                          (Lean.Expr.bvar 0)))
                                      (Lean.Expr.app
                                        (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                        (Lean.Expr.bvar 1)))
                                    (Lean.Expr.app
                                      (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                      (Lean.Expr.bvar 0)))
                                  (Lean.BinderInfo.default))
                                (Lean.BinderInfo.default)))
                            (Lean.Expr.const `TopCat.instConcreteCategoryContinuousMapCarrier [Lean.Level.param `u]))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                    [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                  [Lean.Level.param `u])
                                (Lean.Expr.app
                                  (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                  (Lean.Expr.bvar 5))))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `AlgebraicGeometry.PresheafedSpace.carrier
                                [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                            (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                  [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                [Lean.Level.param `u])
                              (Lean.Expr.app
                                (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                (Lean.Expr.bvar 4))))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.PresheafedSpace.Hom.base
                                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u])
                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                    [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                  [Lean.Level.param `u])
                                (Lean.Expr.app
                                  (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                  (Lean.Expr.bvar 5)))))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                  [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                [Lean.Level.param `u])
                              (Lean.Expr.app
                                (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                (Lean.Expr.bvar 4)))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.Hom.toHom [Lean.Level.param `u])
                              (Lean.Expr.app
                                (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                (Lean.Expr.bvar 5)))
                            (Lean.Expr.app
                              (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                              (Lean.Expr.bvar 4)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `AlgebraicGeometry.Scheme.Hom.toLRSHom' [Lean.Level.param `u])
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.bvar 4))
                            (Lean.Expr.bvar 3))))))
                  (Lean.Expr.bvar 0))))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`CommRingCat.finrank_eq_of_isPushout, (Lean.Expr.forallE
  `R
  (Lean.Expr.const `CommRingCat [Lean.Level.param `u])
  (Lean.Expr.forallE
    `S
    (Lean.Expr.const `CommRingCat [Lean.Level.param `u])
    (Lean.Expr.forallE
      `T
      (Lean.Expr.const `CommRingCat [Lean.Level.param `u])
      (Lean.Expr.forallE
        `P
        (Lean.Expr.const `CommRingCat [Lean.Level.param `u])
        (Lean.Expr.forallE
          `f
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const
                      `CategoryTheory.CategoryStruct.toQuiver
                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `CategoryTheory.Category.toCategoryStruct
                        [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))))
              (Lean.Expr.bvar 3))
            (Lean.Expr.bvar 2))
          (Lean.Expr.forallE
            `g
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `CategoryTheory.CategoryStruct.toQuiver
                        [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const
                          `CategoryTheory.Category.toCategoryStruct
                          [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                      (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))))
                (Lean.Expr.bvar 4))
              (Lean.Expr.bvar 2))
            (Lean.Expr.forallE
              `inl
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const
                          `CategoryTheory.CategoryStruct.toQuiver
                          [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `CategoryTheory.Category.toCategoryStruct
                            [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))))
                  (Lean.Expr.bvar 4))
                (Lean.Expr.bvar 2))
              (Lean.Expr.forallE
                `inr
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Quiver.Hom [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `CategoryTheory.CategoryStruct.toQuiver
                            [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `CategoryTheory.Category.toCategoryStruct
                              [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                          (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))))
                    (Lean.Expr.bvar 4))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.forallE
                  `h
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `CategoryTheory.IsPushout
                                        [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.bvar 4))
                          (Lean.Expr.bvar 3))
                        (Lean.Expr.bvar 2))
                      (Lean.Expr.bvar 1))
                    (Lean.Expr.bvar 0))
                  (Lean.Expr.forallE
                    `hf
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `RingHom.Flat [Lean.Level.param `u, Lean.Level.param `u])
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u])
                                (Lean.Expr.bvar 8)))
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u])
                              (Lean.Expr.bvar 7)))
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRingCat.instCommRingObjForgetRingHomCarrier [Lean.Level.param `u])
                            (Lean.Expr.bvar 8)))
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRingCat.instCommRingObjForgetRingHomCarrier [Lean.Level.param `u])
                          (Lean.Expr.bvar 7)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRingCat.Hom.hom [Lean.Level.param `u])
                            (Lean.Expr.bvar 8))
                          (Lean.Expr.bvar 7))
                        (Lean.Expr.bvar 4)))
                    (Lean.Expr.forallE
                      `hfin
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `RingHom.Finite [Lean.Level.param `u, Lean.Level.param `u])
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u])
                                  (Lean.Expr.bvar 9)))
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u])
                                (Lean.Expr.bvar 8)))
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRingCat.instCommRingObjForgetRingHomCarrier [Lean.Level.param `u])
                              (Lean.Expr.bvar 9)))
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRingCat.instCommRingObjForgetRingHomCarrier [Lean.Level.param `u])
                            (Lean.Expr.bvar 8)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRingCat.Hom.hom [Lean.Level.param `u])
                              (Lean.Expr.bvar 9))
                            (Lean.Expr.bvar 8))
                          (Lean.Expr.bvar 5)))
                      (Lean.Expr.forallE
                        `x
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u])
                              (Lean.Expr.bvar 8)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u])
                                (Lean.Expr.bvar 8)))
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRingCat.instCommRingObjForgetRingHomCarrier [Lean.Level.param `u])
                              (Lean.Expr.bvar 8))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                              (Lean.Expr.const `Nat []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `RingHom.finrank [Lean.Level.param `u, Lean.Level.param `u])
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u])
                                          (Lean.Expr.bvar 9)))
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u])
                                        (Lean.Expr.bvar 8)))
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `CommRingCat.instCommRingObjForgetRingHomCarrier
                                        [Lean.Level.param `u])
                                      (Lean.Expr.bvar 9)))
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `CommRingCat.instCommRingObjForgetRingHomCarrier
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 8)))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRingCat.Hom.hom [Lean.Level.param `u])
                                      (Lean.Expr.bvar 9))
                                    (Lean.Expr.bvar 8))
                                  (Lean.Expr.bvar 4)))
                              (Lean.Expr.bvar 0)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `RingHom.finrank [Lean.Level.param `u, Lean.Level.param `u])
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u])
                                        (Lean.Expr.bvar 11)))
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u])
                                      (Lean.Expr.bvar 10)))
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `CommRingCat.instCommRingObjForgetRingHomCarrier
                                      [Lean.Level.param `u])
                                    (Lean.Expr.bvar 11)))
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `CommRingCat.instCommRingObjForgetRingHomCarrier
                                    [Lean.Level.param `u])
                                  (Lean.Expr.bvar 10)))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRingCat.Hom.hom [Lean.Level.param `u])
                                    (Lean.Expr.bvar 11))
                                  (Lean.Expr.bvar 10))
                                (Lean.Expr.bvar 7)))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `PrimeSpectrum.comap
                                          [Lean.Level.param `u, Lean.Level.param `u])
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u])
                                          (Lean.Expr.bvar 11)))
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u])
                                        (Lean.Expr.bvar 9)))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u])
                                          (Lean.Expr.bvar 11)))
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `CommRingCat.instCommRingObjForgetRingHomCarrier
                                          [Lean.Level.param `u])
                                        (Lean.Expr.bvar 11))))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRingCat.carrier [Lean.Level.param `u])
                                        (Lean.Expr.bvar 9)))
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `CommRingCat.instCommRingObjForgetRingHomCarrier
                                        [Lean.Level.param `u])
                                      (Lean.Expr.bvar 9))))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRingCat.Hom.hom [Lean.Level.param `u])
                                      (Lean.Expr.bvar 11))
                                    (Lean.Expr.bvar 9))
                                  (Lean.Expr.bvar 6)))
                              (Lean.Expr.bvar 0))))
                        (Lean.BinderInfo.default))
                      (Lean.BinderInfo.default))
                    (Lean.BinderInfo.default))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.implicit))
              (Lean.BinderInfo.implicit))
            (Lean.BinderInfo.implicit))
          (Lean.BinderInfo.implicit))
        (Lean.BinderInfo.implicit))
      (Lean.BinderInfo.implicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`Module.Finite.exists_free_surjective, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_1)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 746866052) "_hygCtx") "_hyg") 4)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 746866052) "_hygCtx") "_hyg") 7)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_1]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 746866052) "_hygCtx") "_hyg") 10)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Algebra [Lean.Level.param `u, Lean.Level.param `u_1])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 746866052) "_hygCtx") "_hyg") 14)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Module.Finite [Lean.Level.param `u, Lean.Level.param `u_1])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2))))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_1]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u, Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Exists [Lean.Level.succ (Lean.Level.succ (Lean.Level.param `u))])
                (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u))))
              (Lean.Expr.lam
                `S'
                (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Exists [Lean.Level.succ (Lean.Level.param `u)])
                    (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u]) (Lean.Expr.bvar 0)))
                  (Lean.Expr.lam
                    (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».ThetaStdModuleFinitePresentation 746866052) "_hygCtx") "_hyg") 31)
                    (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u]) (Lean.Expr.bvar 0))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Exists [Lean.Level.succ (Lean.Level.param `u)])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Algebra [Lean.Level.param `u, Lean.Level.param `u])
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.bvar 1))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.bvar 5)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                              (Lean.Expr.bvar 1))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                (Lean.Expr.bvar 1))
                              (Lean.Expr.bvar 0)))))
                      (Lean.Expr.lam
                        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».ThetaStdModuleFinitePresentation 746866052) "_hygCtx") "_hyg") 39)
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Algebra [Lean.Level.param `u, Lean.Level.param `u])
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.bvar 1))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.bvar 5)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                              (Lean.Expr.bvar 1))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                (Lean.Expr.bvar 1))
                              (Lean.Expr.bvar 0))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Exists [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Module.Finite [Lean.Level.param `u, Lean.Level.param `u])
                                      (Lean.Expr.bvar 8))
                                    (Lean.Expr.bvar 2))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                      (Lean.Expr.bvar 8))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                        (Lean.Expr.bvar 8))
                                      (Lean.Expr.bvar 6))))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u])
                                    (Lean.Expr.bvar 2))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                      (Lean.Expr.bvar 2))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                        (Lean.Expr.bvar 2))
                                      (Lean.Expr.bvar 1)))))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u, Lean.Level.param `u])
                                        (Lean.Expr.bvar 8))
                                      (Lean.Expr.bvar 2))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                        (Lean.Expr.bvar 8))
                                      (Lean.Expr.bvar 6)))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                      (Lean.Expr.bvar 2))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                        (Lean.Expr.bvar 2))
                                      (Lean.Expr.bvar 1))))
                                (Lean.Expr.bvar 0))))
                          (Lean.Expr.lam
                            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».ThetaStdModuleFinitePresentation 746866052) "_hygCtx") "_hyg") 48)
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Module.Finite [Lean.Level.param `u, Lean.Level.param `u])
                                      (Lean.Expr.bvar 8))
                                    (Lean.Expr.bvar 2))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                      (Lean.Expr.bvar 8))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                        (Lean.Expr.bvar 8))
                                      (Lean.Expr.bvar 6))))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u])
                                    (Lean.Expr.bvar 2))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                      (Lean.Expr.bvar 2))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                        (Lean.Expr.bvar 2))
                                      (Lean.Expr.bvar 1)))))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u, Lean.Level.param `u])
                                        (Lean.Expr.bvar 8))
                                      (Lean.Expr.bvar 2))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                        (Lean.Expr.bvar 8))
                                      (Lean.Expr.bvar 6)))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                      (Lean.Expr.bvar 2))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                        (Lean.Expr.bvar 2))
                                      (Lean.Expr.bvar 1))))
                                (Lean.Expr.bvar 0)))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Exists [Lean.Level.zero])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Module.Free [Lean.Level.param `u, Lean.Level.param `u])
                                          (Lean.Expr.bvar 9))
                                        (Lean.Expr.bvar 3))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                          (Lean.Expr.bvar 9))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                            (Lean.Expr.bvar 9))
                                          (Lean.Expr.bvar 7))))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u])
                                        (Lean.Expr.bvar 3))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                          (Lean.Expr.bvar 3))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                            (Lean.Expr.bvar 3))
                                          (Lean.Expr.bvar 2)))))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `Algebra.toModule
                                              [Lean.Level.param `u, Lean.Level.param `u])
                                            (Lean.Expr.bvar 9))
                                          (Lean.Expr.bvar 3))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                            (Lean.Expr.bvar 9))
                                          (Lean.Expr.bvar 7)))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                          (Lean.Expr.bvar 3))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                            (Lean.Expr.bvar 3))
                                          (Lean.Expr.bvar 2))))
                                    (Lean.Expr.bvar 1))))
                              (Lean.Expr.lam
                                (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».ThetaStdModuleFinitePresentation 746866052) "_hygCtx") "_hyg") 57)
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Module.Free [Lean.Level.param `u, Lean.Level.param `u])
                                          (Lean.Expr.bvar 9))
                                        (Lean.Expr.bvar 3))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                          (Lean.Expr.bvar 9))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                            (Lean.Expr.bvar 9))
                                          (Lean.Expr.bvar 7))))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u])
                                        (Lean.Expr.bvar 3))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                          (Lean.Expr.bvar 3))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                            (Lean.Expr.bvar 3))
                                          (Lean.Expr.bvar 2)))))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `Algebra.toModule
                                              [Lean.Level.param `u, Lean.Level.param `u])
                                            (Lean.Expr.bvar 9))
                                          (Lean.Expr.bvar 3))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                            (Lean.Expr.bvar 9))
                                          (Lean.Expr.bvar 7)))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                          (Lean.Expr.bvar 3))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                            (Lean.Expr.bvar 3))
                                          (Lean.Expr.bvar 2))))
                                    (Lean.Expr.bvar 1)))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Exists [Lean.Level.zero])
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `Algebra.FinitePresentation
                                                [Lean.Level.param `u, Lean.Level.param `u])
                                              (Lean.Expr.bvar 10))
                                            (Lean.Expr.bvar 4))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                              (Lean.Expr.bvar 10))
                                            (Lean.Expr.bvar 8)))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                            (Lean.Expr.bvar 4))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                              (Lean.Expr.bvar 4))
                                            (Lean.Expr.bvar 3))))
                                      (Lean.Expr.bvar 2)))
                                  (Lean.Expr.lam
                                    (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».ThetaStdModuleFinitePresentation 746866052) "_hygCtx") "_hyg") 66)
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `Algebra.FinitePresentation
                                                [Lean.Level.param `u, Lean.Level.param `u])
                                              (Lean.Expr.bvar 10))
                                            (Lean.Expr.bvar 4))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                              (Lean.Expr.bvar 10))
                                            (Lean.Expr.bvar 8)))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                            (Lean.Expr.bvar 4))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                              (Lean.Expr.bvar 4))
                                            (Lean.Expr.bvar 3))))
                                      (Lean.Expr.bvar 2))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `Exists
                                          [Lean.Level.max
                                             (Lean.Level.succ (Lean.Level.param `u))
                                             (Lean.Level.succ (Lean.Level.param `u_1))])
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `AlgHom
                                                          [Lean.Level.param `u,
                                                           Lean.Level.param `u,
                                                           Lean.Level.param `u_1])
                                                        (Lean.Expr.bvar 11))
                                                      (Lean.Expr.bvar 5))
                                                    (Lean.Expr.bvar 10))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                                      (Lean.Expr.bvar 11))
                                                    (Lean.Expr.bvar 9)))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                                      (Lean.Expr.bvar 5))
                                                    (Lean.Expr.bvar 4))))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                                  (Lean.Expr.bvar 10))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                                    (Lean.Expr.bvar 10))
                                                  (Lean.Expr.bvar 8))))
                                            (Lean.Expr.bvar 3))
                                          (Lean.Expr.bvar 7)))
                                      (Lean.Expr.lam
                                        `f
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `AlgHom
                                                          [Lean.Level.param `u,
                                                           Lean.Level.param `u,
                                                           Lean.Level.param `u_1])
                                                        (Lean.Expr.bvar 11))
                                                      (Lean.Expr.bvar 5))
                                                    (Lean.Expr.bvar 10))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                                      (Lean.Expr.bvar 11))
                                                    (Lean.Expr.bvar 9)))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                                      (Lean.Expr.bvar 5))
                                                    (Lean.Expr.bvar 4))))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                                  (Lean.Expr.bvar 10))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                                    (Lean.Expr.bvar 10))
                                                  (Lean.Expr.bvar 8))))
                                            (Lean.Expr.bvar 3))
                                          (Lean.Expr.bvar 7))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `Function.Surjective
                                                [Lean.Level.succ (Lean.Level.param `u),
                                                 Lean.Level.succ (Lean.Level.param `u_1)])
                                              (Lean.Expr.bvar 6))
                                            (Lean.Expr.bvar 11))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `DFunLike.coe
                                                      [Lean.Level.max
                                                         (Lean.Level.succ (Lean.Level.param `u))
                                                         (Lean.Level.succ (Lean.Level.param `u_1)),
                                                       Lean.Level.succ (Lean.Level.param `u),
                                                       Lean.Level.succ (Lean.Level.param `u_1)])
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgHom
                                                                      [Lean.Level.param `u,
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u_1])
                                                                    (Lean.Expr.bvar 12))
                                                                  (Lean.Expr.bvar 6))
                                                                (Lean.Expr.bvar 11))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `CommRing.toCommSemiring
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.bvar 12))
                                                                (Lean.Expr.bvar 10)))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `CommSemiring.toSemiring
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.bvar 6))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `CommRing.toCommSemiring
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.bvar 6))
                                                                (Lean.Expr.bvar 5))))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `CommSemiring.toSemiring
                                                                [Lean.Level.param `u_1])
                                                              (Lean.Expr.bvar 11))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `CommRing.toCommSemiring
                                                                  [Lean.Level.param `u_1])
                                                                (Lean.Expr.bvar 11))
                                                              (Lean.Expr.bvar 9))))
                                                        (Lean.Expr.bvar 4))
                                                      (Lean.Expr.bvar 8)))
                                                  (Lean.Expr.bvar 6))
                                                (Lean.Expr.lam
                                                  (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                                                  (Lean.Expr.bvar 6)
                                                  (Lean.Expr.bvar 12)
                                                  (Lean.BinderInfo.default)))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgHom.funLike
                                                                [Lean.Level.param `u,
                                                                 Lean.Level.param `u,
                                                                 Lean.Level.param `u_1])
                                                              (Lean.Expr.bvar 12))
                                                            (Lean.Expr.bvar 6))
                                                          (Lean.Expr.bvar 11))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `CommRing.toCommSemiring
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.bvar 12))
                                                          (Lean.Expr.bvar 10)))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `CommSemiring.toSemiring
                                                            [Lean.Level.param `u])
                                                          (Lean.Expr.bvar 6))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `CommRing.toCommSemiring
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.bvar 6))
                                                          (Lean.Expr.bvar 5))))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CommSemiring.toSemiring
                                                          [Lean.Level.param `u_1])
                                                        (Lean.Expr.bvar 11))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `CommRing.toCommSemiring
                                                            [Lean.Level.param `u_1])
                                                          (Lean.Expr.bvar 11))
                                                        (Lean.Expr.bvar 9))))
                                                  (Lean.Expr.bvar 4))
                                                (Lean.Expr.bvar 8)))
                                            (Lean.Expr.bvar 0)))
                                        (Lean.BinderInfo.default)))
                                    (Lean.BinderInfo.default)))
                                (Lean.BinderInfo.default)))
                            (Lean.BinderInfo.default)))
                        (Lean.BinderInfo.default)))
                    (Lean.BinderInfo.default)))
                (Lean.BinderInfo.default)))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))),
  (`Module.FinitePresentation.iff_finitePresentation_of_finite, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_1)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 1621844372) "_hygCtx") "_hyg") 4)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 1621844372) "_hygCtx") "_hyg") 7)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_1]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 1621844372) "_hygCtx") "_hyg") 10)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Algebra [Lean.Level.param `u, Lean.Level.param `u_1])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 1621844372) "_hygCtx") "_hyg") 14)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Module.Finite [Lean.Level.param `u, Lean.Level.param `u_1])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2))))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_1]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u, Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Iff [])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Module.FinitePresentation [Lean.Level.param `u, Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.bvar 3))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                            (Lean.Expr.bvar 4))
                          (Lean.Expr.bvar 2)))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u, Lean.Level.param `u_1])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.bvar 3)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                            (Lean.Expr.bvar 4))
                          (Lean.Expr.bvar 2))))
                    (Lean.Expr.bvar 1))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.FinitePresentation [Lean.Level.param `u, Lean.Level.param `u_1])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 3)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2))))
                (Lean.Expr.bvar 1)))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))),
  (`Module.FinitePresentation.of_finite_of_finitePresentation, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_1)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 23287772) "_hygCtx") "_hyg") 4)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 23287772) "_hygCtx") "_hyg") 7)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_1]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 23287772) "_hygCtx") "_hyg") 10)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Algebra [Lean.Level.param `u, Lean.Level.param `u_1])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 23287772) "_hygCtx") "_hyg") 14)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Module.Finite [Lean.Level.param `u, Lean.Level.param `u_1])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2))))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_1]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u, Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.forallE
              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdModuleFinitePresentation 23287772) "_hygCtx") "_hyg") 18)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.FinitePresentation [Lean.Level.param `u, Lean.Level.param `u_1])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 3)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2))))
                (Lean.Expr.bvar 1))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Module.FinitePresentation [Lean.Level.param `u, Lean.Level.param `u_1])
                        (Lean.Expr.bvar 6))
                      (Lean.Expr.bvar 5))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                        (Lean.Expr.bvar 6))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                          (Lean.Expr.bvar 6))
                        (Lean.Expr.bvar 4))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 5))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3)))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u, Lean.Level.param `u_1])
                          (Lean.Expr.bvar 6))
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                          (Lean.Expr.bvar 6))
                        (Lean.Expr.bvar 4)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3))))
                  (Lean.Expr.bvar 2)))
              (Lean.BinderInfo.instImplicit))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))),
  (`Module.Flat.tfae_algebraMap_surjective, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_1)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_2)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 976855235) "_hygCtx") "_hyg") 4)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_1]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 976855235) "_hygCtx") "_hyg") 7)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_2]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 976855235) "_hygCtx") "_hyg") 10)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Algebra [Lean.Level.param `u_1, Lean.Level.param `u_2])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 976855235) "_hygCtx") "_hyg") 14)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Module.Flat [Lean.Level.param `u_1, Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 2)))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.forallE
              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 976855235) "_hygCtx") "_hyg") 18)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Module.Finite [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2)))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2))))
                  (Lean.Expr.bvar 1)))
              (Lean.Expr.app
                (Lean.Expr.const `List.TFAE [])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.sort (Lean.Level.zero)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `Function.Surjective
                            [Lean.Level.succ (Lean.Level.param `u_1), Lean.Level.succ (Lean.Level.param `u_2)])
                          (Lean.Expr.bvar 6))
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `DFunLike.coe
                                  [Lean.Level.max
                                     (Lean.Level.succ (Lean.Level.param `u_1))
                                     (Lean.Level.succ (Lean.Level.param `u_2)),
                                   Lean.Level.succ (Lean.Level.param `u_1),
                                   Lean.Level.succ (Lean.Level.param `u_2)])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `RingHom [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_1])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                          (Lean.Expr.bvar 6))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                            (Lean.Expr.bvar 6))
                                          (Lean.Expr.bvar 4)))))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_2])
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                        (Lean.Expr.bvar 5))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 5))
                                        (Lean.Expr.bvar 3))))))
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.lam
                              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                              (Lean.Expr.bvar 6)
                              (Lean.Expr.bvar 6)
                              (Lean.BinderInfo.default)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `RingHom.instFunLike [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.bvar 4)))))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 5))
                                  (Lean.Expr.bvar 3))))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Algebra.algebraMap [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 4)))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.bvar 3))))
                          (Lean.Expr.bvar 2)))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.sort (Lean.Level.zero)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `Function.Bijective
                              [Lean.Level.succ (Lean.Level.param `u_2), Lean.Level.succ (Lean.Level.param `u_2)])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `TensorProduct
                                              [Lean.Level.param `u_1, Lean.Level.param `u_2, Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 6))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                              (Lean.Expr.bvar 6))
                                            (Lean.Expr.bvar 4)))
                                        (Lean.Expr.bvar 5))
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `NonUnitalNonAssocSemiring.toAddCommMonoid
                                          [Lean.Level.param `u_2])
                                        (Lean.Expr.bvar 5))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                            [Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 5))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                              [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                [Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `CommRing.toNonUnitalCommRing [Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.bvar 3)))))))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `NonUnitalNonAssocSemiring.toAddCommMonoid
                                        [Lean.Level.param `u_2])
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                          [Lean.Level.param `u_2])
                                        (Lean.Expr.bvar 5))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                            [Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 5))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                              [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toNonUnitalCommRing [Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.bvar 3)))))))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `Algebra.toModule
                                            [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 6))
                                        (Lean.Expr.bvar 5))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                          (Lean.Expr.bvar 6))
                                        (Lean.Expr.bvar 4)))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                        (Lean.Expr.bvar 5))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 5))
                                        (Lean.Expr.bvar 3))))
                                  (Lean.Expr.bvar 2)))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `Algebra.toModule
                                          [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 4)))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                        (Lean.Expr.bvar 5))
                                      (Lean.Expr.bvar 3))))
                                (Lean.Expr.bvar 2))))
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `DFunLike.coe
                                    [Lean.Level.succ (Lean.Level.param `u_2),
                                     Lean.Level.succ (Lean.Level.param `u_2),
                                     Lean.Level.succ (Lean.Level.param `u_2)])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `LinearMap
                                                          [Lean.Level.param `u_1,
                                                           Lean.Level.param `u_1,
                                                           Lean.Level.param `u_2,
                                                           Lean.Level.param `u_2])
                                                        (Lean.Expr.bvar 6))
                                                      (Lean.Expr.bvar 6))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CommSemiring.toSemiring
                                                          [Lean.Level.param `u_1])
                                                        (Lean.Expr.bvar 6))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `CommRing.toCommSemiring
                                                            [Lean.Level.param `u_1])
                                                          (Lean.Expr.bvar 6))
                                                        (Lean.Expr.bvar 4))))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                                      (Lean.Expr.bvar 6))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CommRing.toCommSemiring
                                                          [Lean.Level.param `u_1])
                                                        (Lean.Expr.bvar 6))
                                                      (Lean.Expr.bvar 4))))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `RingHom.id [Lean.Level.param `u_1])
                                                    (Lean.Expr.bvar 6))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `Semiring.toNonAssocSemiring
                                                        [Lean.Level.param `u_1])
                                                      (Lean.Expr.bvar 6))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CommSemiring.toSemiring
                                                          [Lean.Level.param `u_1])
                                                        (Lean.Expr.bvar 6))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `CommRing.toCommSemiring
                                                            [Lean.Level.param `u_1])
                                                          (Lean.Expr.bvar 6))
                                                        (Lean.Expr.bvar 4))))))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `TensorProduct
                                                                [Lean.Level.param `u_1,
                                                                 Lean.Level.param `u_2,
                                                                 Lean.Level.param `u_2])
                                                              (Lean.Expr.bvar 6))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `CommRing.toCommSemiring
                                                                  [Lean.Level.param `u_1])
                                                                (Lean.Expr.bvar 6))
                                                              (Lean.Expr.bvar 4)))
                                                          (Lean.Expr.bvar 5))
                                                        (Lean.Expr.bvar 5))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `NonUnitalNonAssocSemiring.toAddCommMonoid
                                                            [Lean.Level.param `u_2])
                                                          (Lean.Expr.bvar 5))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                                              [Lean.Level.param `u_2])
                                                            (Lean.Expr.bvar 5))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                                [Lean.Level.param `u_2])
                                                              (Lean.Expr.bvar 5))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                                  [Lean.Level.param `u_2])
                                                                (Lean.Expr.bvar 5))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `CommRing.toNonUnitalCommRing
                                                                    [Lean.Level.param `u_2])
                                                                  (Lean.Expr.bvar 5))
                                                                (Lean.Expr.bvar 3)))))))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `NonUnitalNonAssocSemiring.toAddCommMonoid
                                                          [Lean.Level.param `u_2])
                                                        (Lean.Expr.bvar 5))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                                            [Lean.Level.param `u_2])
                                                          (Lean.Expr.bvar 5))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                              [Lean.Level.param `u_2])
                                                            (Lean.Expr.bvar 5))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                                [Lean.Level.param `u_2])
                                                              (Lean.Expr.bvar 5))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `CommRing.toNonUnitalCommRing
                                                                  [Lean.Level.param `u_2])
                                                                (Lean.Expr.bvar 5))
                                                              (Lean.Expr.bvar 3)))))))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `Algebra.toModule
                                                              [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                                            (Lean.Expr.bvar 6))
                                                          (Lean.Expr.bvar 5))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `CommRing.toCommSemiring
                                                              [Lean.Level.param `u_1])
                                                            (Lean.Expr.bvar 6))
                                                          (Lean.Expr.bvar 4)))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `CommSemiring.toSemiring
                                                            [Lean.Level.param `u_2])
                                                          (Lean.Expr.bvar 5))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `CommRing.toCommSemiring
                                                              [Lean.Level.param `u_2])
                                                            (Lean.Expr.bvar 5))
                                                          (Lean.Expr.bvar 3))))
                                                    (Lean.Expr.bvar 2)))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `Algebra.toModule
                                                            [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                                          (Lean.Expr.bvar 6))
                                                        (Lean.Expr.bvar 5))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `CommRing.toCommSemiring
                                                            [Lean.Level.param `u_1])
                                                          (Lean.Expr.bvar 6))
                                                        (Lean.Expr.bvar 4)))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CommSemiring.toSemiring
                                                          [Lean.Level.param `u_2])
                                                        (Lean.Expr.bvar 5))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `CommRing.toCommSemiring
                                                            [Lean.Level.param `u_2])
                                                          (Lean.Expr.bvar 5))
                                                        (Lean.Expr.bvar 3))))
                                                  (Lean.Expr.bvar 2))))
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `TensorProduct.addCommMonoid
                                                            [Lean.Level.param `u_1,
                                                             Lean.Level.param `u_2,
                                                             Lean.Level.param `u_2])
                                                          (Lean.Expr.bvar 6))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `CommRing.toCommSemiring
                                                              [Lean.Level.param `u_1])
                                                            (Lean.Expr.bvar 6))
                                                          (Lean.Expr.bvar 4)))
                                                      (Lean.Expr.bvar 5))
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `NonUnitalNonAssocSemiring.toAddCommMonoid
                                                        [Lean.Level.param `u_2])
                                                      (Lean.Expr.bvar 5))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                                          [Lean.Level.param `u_2])
                                                        (Lean.Expr.bvar 5))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                            [Lean.Level.param `u_2])
                                                          (Lean.Expr.bvar 5))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                              [Lean.Level.param `u_2])
                                                            (Lean.Expr.bvar 5))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `CommRing.toNonUnitalCommRing
                                                                [Lean.Level.param `u_2])
                                                              (Lean.Expr.bvar 5))
                                                            (Lean.Expr.bvar 3)))))))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `NonUnitalNonAssocSemiring.toAddCommMonoid
                                                      [Lean.Level.param `u_2])
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                                        [Lean.Level.param `u_2])
                                                      (Lean.Expr.bvar 5))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                          [Lean.Level.param `u_2])
                                                        (Lean.Expr.bvar 5))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                            [Lean.Level.param `u_2])
                                                          (Lean.Expr.bvar 5))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `CommRing.toNonUnitalCommRing
                                                              [Lean.Level.param `u_2])
                                                            (Lean.Expr.bvar 5))
                                                          (Lean.Expr.bvar 3)))))))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `Algebra.toModule
                                                          [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                                        (Lean.Expr.bvar 6))
                                                      (Lean.Expr.bvar 5))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CommRing.toCommSemiring
                                                          [Lean.Level.param `u_1])
                                                        (Lean.Expr.bvar 6))
                                                      (Lean.Expr.bvar 4)))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                                      (Lean.Expr.bvar 5))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CommRing.toCommSemiring
                                                          [Lean.Level.param `u_2])
                                                        (Lean.Expr.bvar 5))
                                                      (Lean.Expr.bvar 3))))
                                                (Lean.Expr.bvar 2)))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `Algebra.toModule
                                                        [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                                      (Lean.Expr.bvar 6))
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                                      (Lean.Expr.bvar 6))
                                                    (Lean.Expr.bvar 4)))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                                      (Lean.Expr.bvar 5))
                                                    (Lean.Expr.bvar 3))))
                                              (Lean.Expr.bvar 2))))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `NonUnitalNonAssocSemiring.toAddCommMonoid
                                              [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                                [Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                  [Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                    [Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `CommRing.toNonUnitalCommRing
                                                      [Lean.Level.param `u_2])
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.bvar 3)))))))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `TensorProduct.instModule
                                                        [Lean.Level.param `u_1,
                                                         Lean.Level.param `u_2,
                                                         Lean.Level.param `u_2])
                                                      (Lean.Expr.bvar 6))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CommRing.toCommSemiring
                                                          [Lean.Level.param `u_1])
                                                        (Lean.Expr.bvar 6))
                                                      (Lean.Expr.bvar 4)))
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `NonUnitalNonAssocSemiring.toAddCommMonoid
                                                    [Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                                      [Lean.Level.param `u_2])
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                        [Lean.Level.param `u_2])
                                                      (Lean.Expr.bvar 5))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                          [Lean.Level.param `u_2])
                                                        (Lean.Expr.bvar 5))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `CommRing.toNonUnitalCommRing
                                                            [Lean.Level.param `u_2])
                                                          (Lean.Expr.bvar 5))
                                                        (Lean.Expr.bvar 3)))))))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `NonUnitalNonAssocSemiring.toAddCommMonoid
                                                  [Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                                    [Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                      [Lean.Level.param `u_2])
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                        [Lean.Level.param `u_2])
                                                      (Lean.Expr.bvar 5))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CommRing.toNonUnitalCommRing
                                                          [Lean.Level.param `u_2])
                                                        (Lean.Expr.bvar 5))
                                                      (Lean.Expr.bvar 3)))))))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `Algebra.toModule
                                                      [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                                    (Lean.Expr.bvar 6))
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                                    (Lean.Expr.bvar 6))
                                                  (Lean.Expr.bvar 4)))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.bvar 3))))
                                            (Lean.Expr.bvar 2)))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `Algebra.toModule
                                                    [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 6))
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                                  (Lean.Expr.bvar 6))
                                                (Lean.Expr.bvar 4)))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.bvar 3))))
                                          (Lean.Expr.bvar 2))))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `Algebra.toModule
                                                [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 6))
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                              (Lean.Expr.bvar 6))
                                            (Lean.Expr.bvar 4)))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.bvar 3))))
                                      (Lean.Expr.bvar 2))))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `TensorProduct
                                                  [Lean.Level.param `u_1, Lean.Level.param `u_2, Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 6))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                                  (Lean.Expr.bvar 6))
                                                (Lean.Expr.bvar 4)))
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.bvar 5))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `NonUnitalNonAssocSemiring.toAddCommMonoid
                                              [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                                [Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                  [Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                    [Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `CommRing.toNonUnitalCommRing
                                                      [Lean.Level.param `u_2])
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.bvar 3)))))))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `NonUnitalNonAssocSemiring.toAddCommMonoid
                                            [Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 5))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                              [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                [Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                  [Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `CommRing.toNonUnitalCommRing
                                                    [Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.bvar 3)))))))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `Algebra.toModule
                                                [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 6))
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                              (Lean.Expr.bvar 6))
                                            (Lean.Expr.bvar 4)))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.bvar 3))))
                                      (Lean.Expr.bvar 2)))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `Algebra.toModule
                                              [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 6))
                                          (Lean.Expr.bvar 5))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                            (Lean.Expr.bvar 6))
                                          (Lean.Expr.bvar 4)))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 5))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.bvar 3))))
                                    (Lean.Expr.bvar 2))))
                              (Lean.Expr.lam
                                (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `TensorProduct
                                                  [Lean.Level.param `u_1, Lean.Level.param `u_2, Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 6))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                                  (Lean.Expr.bvar 6))
                                                (Lean.Expr.bvar 4)))
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.bvar 5))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `NonUnitalNonAssocSemiring.toAddCommMonoid
                                              [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                                [Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                  [Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                    [Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `CommRing.toNonUnitalCommRing
                                                      [Lean.Level.param `u_2])
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.bvar 3)))))))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `NonUnitalNonAssocSemiring.toAddCommMonoid
                                            [Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 5))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                              [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                [Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                  [Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `CommRing.toNonUnitalCommRing
                                                    [Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.bvar 3)))))))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `Algebra.toModule
                                                [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 6))
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                              (Lean.Expr.bvar 6))
                                            (Lean.Expr.bvar 4)))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.bvar 3))))
                                      (Lean.Expr.bvar 2)))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `Algebra.toModule
                                              [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 6))
                                          (Lean.Expr.bvar 5))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                            (Lean.Expr.bvar 6))
                                          (Lean.Expr.bvar 4)))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 5))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.bvar 3))))
                                    (Lean.Expr.bvar 2)))
                                (Lean.Expr.bvar 6)
                                (Lean.BinderInfo.default)))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `LinearMap.instFunLike
                                                    [Lean.Level.param `u_1,
                                                     Lean.Level.param `u_1,
                                                     Lean.Level.param `u_2,
                                                     Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 6))
                                                (Lean.Expr.bvar 6))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `TensorProduct
                                                                [Lean.Level.param `u_1,
                                                                 Lean.Level.param `u_2,
                                                                 Lean.Level.param `u_2])
                                                              (Lean.Expr.bvar 6))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `CommRing.toCommSemiring
                                                                  [Lean.Level.param `u_1])
                                                                (Lean.Expr.bvar 6))
                                                              (Lean.Expr.bvar 4)))
                                                          (Lean.Expr.bvar 5))
                                                        (Lean.Expr.bvar 5))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `NonUnitalNonAssocSemiring.toAddCommMonoid
                                                            [Lean.Level.param `u_2])
                                                          (Lean.Expr.bvar 5))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                                              [Lean.Level.param `u_2])
                                                            (Lean.Expr.bvar 5))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                                [Lean.Level.param `u_2])
                                                              (Lean.Expr.bvar 5))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                                  [Lean.Level.param `u_2])
                                                                (Lean.Expr.bvar 5))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `CommRing.toNonUnitalCommRing
                                                                    [Lean.Level.param `u_2])
                                                                  (Lean.Expr.bvar 5))
                                                                (Lean.Expr.bvar 3)))))))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `NonUnitalNonAssocSemiring.toAddCommMonoid
                                                          [Lean.Level.param `u_2])
                                                        (Lean.Expr.bvar 5))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                                            [Lean.Level.param `u_2])
                                                          (Lean.Expr.bvar 5))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                              [Lean.Level.param `u_2])
                                                            (Lean.Expr.bvar 5))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                                [Lean.Level.param `u_2])
                                                              (Lean.Expr.bvar 5))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `CommRing.toNonUnitalCommRing
                                                                  [Lean.Level.param `u_2])
                                                                (Lean.Expr.bvar 5))
                                                              (Lean.Expr.bvar 3)))))))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `Algebra.toModule
                                                              [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                                            (Lean.Expr.bvar 6))
                                                          (Lean.Expr.bvar 5))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `CommRing.toCommSemiring
                                                              [Lean.Level.param `u_1])
                                                            (Lean.Expr.bvar 6))
                                                          (Lean.Expr.bvar 4)))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `CommSemiring.toSemiring
                                                            [Lean.Level.param `u_2])
                                                          (Lean.Expr.bvar 5))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `CommRing.toCommSemiring
                                                              [Lean.Level.param `u_2])
                                                            (Lean.Expr.bvar 5))
                                                          (Lean.Expr.bvar 3))))
                                                    (Lean.Expr.bvar 2)))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `Algebra.toModule
                                                            [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                                          (Lean.Expr.bvar 6))
                                                        (Lean.Expr.bvar 5))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `CommRing.toCommSemiring
                                                            [Lean.Level.param `u_1])
                                                          (Lean.Expr.bvar 6))
                                                        (Lean.Expr.bvar 4)))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CommSemiring.toSemiring
                                                          [Lean.Level.param `u_2])
                                                        (Lean.Expr.bvar 5))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `CommRing.toCommSemiring
                                                            [Lean.Level.param `u_2])
                                                          (Lean.Expr.bvar 5))
                                                        (Lean.Expr.bvar 3))))
                                                  (Lean.Expr.bvar 2))))
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                              (Lean.Expr.bvar 6))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                                (Lean.Expr.bvar 6))
                                              (Lean.Expr.bvar 4))))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                            (Lean.Expr.bvar 6))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                              (Lean.Expr.bvar 6))
                                            (Lean.Expr.bvar 4))))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `TensorProduct.addCommMonoid
                                                        [Lean.Level.param `u_1,
                                                         Lean.Level.param `u_2,
                                                         Lean.Level.param `u_2])
                                                      (Lean.Expr.bvar 6))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CommRing.toCommSemiring
                                                          [Lean.Level.param `u_1])
                                                        (Lean.Expr.bvar 6))
                                                      (Lean.Expr.bvar 4)))
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `NonUnitalNonAssocSemiring.toAddCommMonoid
                                                    [Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                                      [Lean.Level.param `u_2])
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                        [Lean.Level.param `u_2])
                                                      (Lean.Expr.bvar 5))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                          [Lean.Level.param `u_2])
                                                        (Lean.Expr.bvar 5))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `CommRing.toNonUnitalCommRing
                                                            [Lean.Level.param `u_2])
                                                          (Lean.Expr.bvar 5))
                                                        (Lean.Expr.bvar 3)))))))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `NonUnitalNonAssocSemiring.toAddCommMonoid
                                                  [Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                                    [Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                      [Lean.Level.param `u_2])
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                        [Lean.Level.param `u_2])
                                                      (Lean.Expr.bvar 5))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CommRing.toNonUnitalCommRing
                                                          [Lean.Level.param `u_2])
                                                        (Lean.Expr.bvar 5))
                                                      (Lean.Expr.bvar 3)))))))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `Algebra.toModule
                                                      [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                                    (Lean.Expr.bvar 6))
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                                    (Lean.Expr.bvar 6))
                                                  (Lean.Expr.bvar 4)))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.bvar 3))))
                                            (Lean.Expr.bvar 2)))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `Algebra.toModule
                                                    [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 6))
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                                  (Lean.Expr.bvar 6))
                                                (Lean.Expr.bvar 4)))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.bvar 3))))
                                          (Lean.Expr.bvar 2))))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `NonUnitalNonAssocSemiring.toAddCommMonoid
                                          [Lean.Level.param `u_2])
                                        (Lean.Expr.bvar 5))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                            [Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 5))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                              [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                [Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `CommRing.toNonUnitalCommRing [Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.bvar 3)))))))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `TensorProduct.instModule
                                                    [Lean.Level.param `u_1,
                                                     Lean.Level.param `u_2,
                                                     Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 6))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                                    (Lean.Expr.bvar 6))
                                                  (Lean.Expr.bvar 4)))
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `NonUnitalNonAssocSemiring.toAddCommMonoid
                                                [Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                                  [Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                    [Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                      [Lean.Level.param `u_2])
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `CommRing.toNonUnitalCommRing
                                                        [Lean.Level.param `u_2])
                                                      (Lean.Expr.bvar 5))
                                                    (Lean.Expr.bvar 3)))))))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `NonUnitalNonAssocSemiring.toAddCommMonoid
                                              [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                                [Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                                  [Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                                    [Lean.Level.param `u_2])
                                                  (Lean.Expr.bvar 5))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `CommRing.toNonUnitalCommRing
                                                      [Lean.Level.param `u_2])
                                                    (Lean.Expr.bvar 5))
                                                  (Lean.Expr.bvar 3)))))))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `Algebra.toModule
                                                  [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 6))
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                                (Lean.Expr.bvar 6))
                                              (Lean.Expr.bvar 4)))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                                (Lean.Expr.bvar 5))
                                              (Lean.Expr.bvar 3))))
                                        (Lean.Expr.bvar 2)))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `Algebra.toModule
                                                [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 6))
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                              (Lean.Expr.bvar 6))
                                            (Lean.Expr.bvar 4)))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                              (Lean.Expr.bvar 5))
                                            (Lean.Expr.bvar 3))))
                                      (Lean.Expr.bvar 2))))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `Algebra.toModule
                                            [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 6))
                                        (Lean.Expr.bvar 5))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                          (Lean.Expr.bvar 6))
                                        (Lean.Expr.bvar 4)))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                        (Lean.Expr.bvar 5))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 5))
                                        (Lean.Expr.bvar 3))))
                                  (Lean.Expr.bvar 2)))
                              (Lean.Expr.app
                                (Lean.Expr.app (Lean.Expr.const `RingHom.id [Lean.Level.param `u_1]) (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_1])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 4)))))))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `LinearMap.mul' [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 4)))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                                        [Lean.Level.param `u_2])
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                                          [Lean.Level.param `u_2])
                                        (Lean.Expr.bvar 5))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `NonUnitalCommRing.toNonUnitalNonAssocCommRing
                                            [Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 5))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toNonUnitalCommRing [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.bvar 3))))))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `Algebra.toModule
                                            [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 6))
                                        (Lean.Expr.bvar 5))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                          (Lean.Expr.bvar 6))
                                        (Lean.Expr.bvar 4)))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                        (Lean.Expr.bvar 5))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 5))
                                        (Lean.Expr.bvar 3))))
                                  (Lean.Expr.bvar 2)))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `Algebra.to_smulCommClass
                                          [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 4)))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                        (Lean.Expr.bvar 5))
                                      (Lean.Expr.bvar 3))))
                                (Lean.Expr.bvar 2)))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `IsScalarTower.right
                                        [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.bvar 5))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.bvar 4)))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 5))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.bvar 3))))
                              (Lean.Expr.bvar 2))))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `List.cons [Lean.Level.zero])
                          (Lean.Expr.sort (Lean.Level.zero)))
                        (Lean.Expr.forallE
                          `p
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1]) (Lean.Expr.bvar 6))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 4)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                                (Lean.Expr.const `instLENat []))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `Module.rankAtStalk
                                            [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 7))
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Ring.toAddCommGroup [Lean.Level.param `u_2])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRing.toRing [Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 6))
                                        (Lean.Expr.bvar 4))))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `Algebra.toModule
                                              [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 7))
                                          (Lean.Expr.bvar 6))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                            (Lean.Expr.bvar 7))
                                          (Lean.Expr.bvar 5)))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                          (Lean.Expr.bvar 6))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                            (Lean.Expr.bvar 6))
                                          (Lean.Expr.bvar 4))))
                                    (Lean.Expr.bvar 3)))
                                (Lean.Expr.bvar 0)))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero])
                                  (Lean.Expr.const `Nat []))
                                (Lean.Expr.lit (Lean.Literal.natVal 1)))
                              (Lean.Expr.app
                                (Lean.Expr.const `instOfNatNat [])
                                (Lean.Expr.lit (Lean.Literal.natVal 1)))))
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.app
                        (Lean.Expr.const `List.nil [Lean.Level.zero])
                        (Lean.Expr.sort (Lean.Level.zero)))))))
              (Lean.BinderInfo.instImplicit))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))),
  (`Module.algebraMap_bijective_iff_rankAtStalk, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_1)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_2)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 4141729317) "_hygCtx") "_hyg") 4)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_1]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 4141729317) "_hygCtx") "_hyg") 7)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_2]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 4141729317) "_hygCtx") "_hyg") 10)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Algebra [Lean.Level.param `u_1, Lean.Level.param `u_2])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 4141729317) "_hygCtx") "_hyg") 14)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Module.Flat [Lean.Level.param `u_1, Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 2)))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.forallE
              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 4141729317) "_hygCtx") "_hyg") 18)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Module.Finite [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2)))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2))))
                  (Lean.Expr.bvar 1)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Iff [])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.param `u_1)])
                        (Lean.Expr.forallE
                          `p
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1]) (Lean.Expr.bvar 6))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 4)))
                          (Lean.Expr.const `Nat [])
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Module.rankAtStalk [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.bvar 4))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Ring.toAddCommGroup [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toRing [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.bvar 3))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 4)))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.bvar 3))))
                          (Lean.Expr.bvar 2))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `OfNat.ofNat [Lean.Level.param `u_1])
                          (Lean.Expr.forallE
                            `p
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 4)))
                            (Lean.Expr.const `Nat [])
                            (Lean.BinderInfo.default)))
                        (Lean.Expr.lit (Lean.Literal.natVal 1)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `One.toOfNat1 [Lean.Level.param `u_1])
                          (Lean.Expr.forallE
                            `p
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 4)))
                            (Lean.Expr.const `Nat [])
                            (Lean.BinderInfo.default)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Pi.instOne [Lean.Level.param `u_1, Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 4))))
                            (Lean.Expr.lam
                              `p
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 4)))
                              (Lean.Expr.const `Nat [])
                              (Lean.BinderInfo.default)))
                          (Lean.Expr.lam
                            `i
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 4)))
                            (Lean.Expr.const `Nat.instOne [])
                            (Lean.BinderInfo.default)))))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `Function.Bijective
                        [Lean.Level.succ (Lean.Level.param `u_1), Lean.Level.succ (Lean.Level.param `u_2)])
                      (Lean.Expr.bvar 6))
                    (Lean.Expr.bvar 5))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `DFunLike.coe
                              [Lean.Level.max
                                 (Lean.Level.succ (Lean.Level.param `u_1))
                                 (Lean.Level.succ (Lean.Level.param `u_2)),
                               Lean.Level.succ (Lean.Level.param `u_1),
                               Lean.Level.succ (Lean.Level.param `u_2)])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `RingHom [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_1])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 4)))))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 5))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.bvar 3))))))
                          (Lean.Expr.bvar 6))
                        (Lean.Expr.lam
                          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                          (Lean.Expr.bvar 6)
                          (Lean.Expr.bvar 6)
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `RingHom.instFunLike [Lean.Level.param `u_1, Lean.Level.param `u_2])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_1])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 4)))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_2])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.bvar 3))))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Algebra.algebraMap [Lean.Level.param `u_1, Lean.Level.param `u_2])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 4)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.bvar 3))))
                      (Lean.Expr.bvar 2)))))
              (Lean.BinderInfo.instImplicit))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`Module.algebraMap_bijective_of_rankAtStalk, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_1)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_2)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 4141729317) "_hygCtx") "_hyg") 4)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_1]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 4141729317) "_hygCtx") "_hyg") 7)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_2]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 4141729317) "_hygCtx") "_hyg") 10)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Algebra [Lean.Level.param `u_1, Lean.Level.param `u_2])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 4141729317) "_hygCtx") "_hyg") 14)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Module.Flat [Lean.Level.param `u_1, Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 2)))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.forallE
              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 4141729317) "_hygCtx") "_hyg") 18)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Module.Finite [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2)))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2))))
                  (Lean.Expr.bvar 1)))
              (Lean.Expr.forallE
                (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.param `u_1)])
                      (Lean.Expr.forallE
                        `p
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1]) (Lean.Expr.bvar 6))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 4)))
                        (Lean.Expr.const `Nat [])
                        (Lean.BinderInfo.default)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Module.rankAtStalk [Lean.Level.param `u_1, Lean.Level.param `u_2])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Ring.toAddCommGroup [Lean.Level.param `u_2])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toRing [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.bvar 3))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 4)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.bvar 3))))
                        (Lean.Expr.bvar 2))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `OfNat.ofNat [Lean.Level.param `u_1])
                        (Lean.Expr.forallE
                          `p
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1]) (Lean.Expr.bvar 6))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 4)))
                          (Lean.Expr.const `Nat [])
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.lit (Lean.Literal.natVal 1)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `One.toOfNat1 [Lean.Level.param `u_1])
                        (Lean.Expr.forallE
                          `p
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1]) (Lean.Expr.bvar 6))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 4)))
                          (Lean.Expr.const `Nat [])
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Pi.instOne [Lean.Level.param `u_1, Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 4))))
                          (Lean.Expr.lam
                            `p
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 4)))
                            (Lean.Expr.const `Nat [])
                            (Lean.BinderInfo.default)))
                        (Lean.Expr.lam
                          `i
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1]) (Lean.Expr.bvar 6))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 4)))
                          (Lean.Expr.const `Nat.instOne [])
                          (Lean.BinderInfo.default))))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `Function.Bijective
                        [Lean.Level.succ (Lean.Level.param `u_1), Lean.Level.succ (Lean.Level.param `u_2)])
                      (Lean.Expr.bvar 7))
                    (Lean.Expr.bvar 6))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `DFunLike.coe
                              [Lean.Level.max
                                 (Lean.Level.succ (Lean.Level.param `u_1))
                                 (Lean.Level.succ (Lean.Level.param `u_2)),
                               Lean.Level.succ (Lean.Level.param `u_1),
                               Lean.Level.succ (Lean.Level.param `u_2)])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `RingHom [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_1])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                      (Lean.Expr.bvar 7))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                        (Lean.Expr.bvar 7))
                                      (Lean.Expr.bvar 5)))))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.bvar 4))))))
                          (Lean.Expr.bvar 7))
                        (Lean.Expr.lam
                          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                          (Lean.Expr.bvar 7)
                          (Lean.Expr.bvar 7)
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `RingHom.instFunLike [Lean.Level.param `u_1, Lean.Level.param `u_2])
                              (Lean.Expr.bvar 7))
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_1])
                              (Lean.Expr.bvar 7))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.bvar 5)))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_2])
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 4))))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Algebra.algebraMap [Lean.Level.param `u_1, Lean.Level.param `u_2])
                              (Lean.Expr.bvar 7))
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                              (Lean.Expr.bvar 7))
                            (Lean.Expr.bvar 5)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 4))))
                      (Lean.Expr.bvar 3))))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.instImplicit))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`Module.algebraMap_surjective_of_rankAtStalk_le_one, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_1)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_2)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 3633274504) "_hygCtx") "_hyg") 4)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_1]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 3633274504) "_hygCtx") "_hyg") 7)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_2]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 3633274504) "_hygCtx") "_hyg") 10)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Algebra [Lean.Level.param `u_1, Lean.Level.param `u_2])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 3633274504) "_hygCtx") "_hyg") 14)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Module.Flat [Lean.Level.param `u_1, Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 2)))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.forallE
              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 3633274504) "_hygCtx") "_hyg") 18)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Module.Finite [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2)))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2))))
                  (Lean.Expr.bvar 1)))
              (Lean.Expr.forallE
                `h
                (Lean.Expr.forallE
                  `p
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1]) (Lean.Expr.bvar 6))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 6))
                      (Lean.Expr.bvar 4)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `instLENat []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Module.rankAtStalk [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Ring.toAddCommGroup [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toRing [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 4))))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 5)))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 4))))
                            (Lean.Expr.bvar 3)))
                        (Lean.Expr.bvar 0)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                        (Lean.Expr.lit (Lean.Literal.natVal 1)))
                      (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))
                  (Lean.BinderInfo.default))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `Function.Surjective
                        [Lean.Level.succ (Lean.Level.param `u_1), Lean.Level.succ (Lean.Level.param `u_2)])
                      (Lean.Expr.bvar 7))
                    (Lean.Expr.bvar 6))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `DFunLike.coe
                              [Lean.Level.max
                                 (Lean.Level.succ (Lean.Level.param `u_1))
                                 (Lean.Level.succ (Lean.Level.param `u_2)),
                               Lean.Level.succ (Lean.Level.param `u_1),
                               Lean.Level.succ (Lean.Level.param `u_2)])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `RingHom [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_1])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                      (Lean.Expr.bvar 7))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                        (Lean.Expr.bvar 7))
                                      (Lean.Expr.bvar 5)))))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.bvar 4))))))
                          (Lean.Expr.bvar 7))
                        (Lean.Expr.lam
                          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                          (Lean.Expr.bvar 7)
                          (Lean.Expr.bvar 7)
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `RingHom.instFunLike [Lean.Level.param `u_1, Lean.Level.param `u_2])
                              (Lean.Expr.bvar 7))
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_1])
                              (Lean.Expr.bvar 7))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.bvar 5)))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_2])
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 4))))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Algebra.algebraMap [Lean.Level.param `u_1, Lean.Level.param `u_2])
                              (Lean.Expr.bvar 7))
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                              (Lean.Expr.bvar 7))
                            (Lean.Expr.bvar 5)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 4))))
                      (Lean.Expr.bvar 3))))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.instImplicit))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`Module.rankAtStalk_le_one_iff_surjective, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_1)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_2)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 736312635) "_hygCtx") "_hyg") 4)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_1]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 736312635) "_hygCtx") "_hyg") 7)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_2]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 736312635) "_hygCtx") "_hyg") 10)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Algebra [Lean.Level.param `u_1, Lean.Level.param `u_2])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 736312635) "_hygCtx") "_hyg") 14)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Module.Flat [Lean.Level.param `u_1, Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 2)))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.forallE
              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 736312635) "_hygCtx") "_hyg") 18)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Module.Finite [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2)))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2))))
                  (Lean.Expr.bvar 1)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Iff [])
                  (Lean.Expr.forallE
                    `p
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1]) (Lean.Expr.bvar 6))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 6))
                        (Lean.Expr.bvar 4)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                          (Lean.Expr.const `instLENat []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Module.rankAtStalk [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Ring.toAddCommGroup [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRing.toRing [Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 4))))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                      (Lean.Expr.bvar 7))
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                      (Lean.Expr.bvar 7))
                                    (Lean.Expr.bvar 5)))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.bvar 4))))
                              (Lean.Expr.bvar 3)))
                          (Lean.Expr.bvar 0)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                          (Lean.Expr.lit (Lean.Literal.natVal 1)))
                        (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))
                    (Lean.BinderInfo.default)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `Function.Surjective
                        [Lean.Level.succ (Lean.Level.param `u_1), Lean.Level.succ (Lean.Level.param `u_2)])
                      (Lean.Expr.bvar 6))
                    (Lean.Expr.bvar 5))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `DFunLike.coe
                              [Lean.Level.max
                                 (Lean.Level.succ (Lean.Level.param `u_1))
                                 (Lean.Level.succ (Lean.Level.param `u_2)),
                               Lean.Level.succ (Lean.Level.param `u_1),
                               Lean.Level.succ (Lean.Level.param `u_2)])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `RingHom [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_1])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 4)))))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 5))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.bvar 3))))))
                          (Lean.Expr.bvar 6))
                        (Lean.Expr.lam
                          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                          (Lean.Expr.bvar 6)
                          (Lean.Expr.bvar 6)
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `RingHom.instFunLike [Lean.Level.param `u_1, Lean.Level.param `u_2])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_1])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 4)))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_2])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.bvar 3))))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Algebra.algebraMap [Lean.Level.param `u_1, Lean.Level.param `u_2])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 4)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.bvar 3))))
                      (Lean.Expr.bvar 2)))))
              (Lean.BinderInfo.instImplicit))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`Module.rankAtStalk_pos_iff_algebraMap_injective, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_1)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_2)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 3579572697) "_hygCtx") "_hyg") 4)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_1]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 3579572697) "_hygCtx") "_hyg") 7)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_2]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 3579572697) "_hygCtx") "_hyg") 10)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Algebra [Lean.Level.param `u_1, Lean.Level.param `u_2])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 3579572697) "_hygCtx") "_hyg") 14)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Module.Flat [Lean.Level.param `u_1, Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 2)))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.forallE
              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 3579572697) "_hygCtx") "_hyg") 18)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Module.Finite [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2)))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2))))
                  (Lean.Expr.bvar 1)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Iff [])
                  (Lean.Expr.forallE
                    `p
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1]) (Lean.Expr.bvar 6))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 6))
                        (Lean.Expr.bvar 4)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                          (Lean.Expr.const `instLTNat []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                            (Lean.Expr.lit (Lean.Literal.natVal 0)))
                          (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 0)))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Module.rankAtStalk [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Ring.toAddCommGroup [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toRing [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 4))))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 5)))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 4))))
                            (Lean.Expr.bvar 3)))
                        (Lean.Expr.bvar 0)))
                    (Lean.BinderInfo.default)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `Function.Injective
                        [Lean.Level.succ (Lean.Level.param `u_1), Lean.Level.succ (Lean.Level.param `u_2)])
                      (Lean.Expr.bvar 6))
                    (Lean.Expr.bvar 5))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `DFunLike.coe
                              [Lean.Level.max
                                 (Lean.Level.succ (Lean.Level.param `u_1))
                                 (Lean.Level.succ (Lean.Level.param `u_2)),
                               Lean.Level.succ (Lean.Level.param `u_1),
                               Lean.Level.succ (Lean.Level.param `u_2)])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `RingHom [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_1])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 4)))))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 5))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.bvar 3))))))
                          (Lean.Expr.bvar 6))
                        (Lean.Expr.lam
                          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                          (Lean.Expr.bvar 6)
                          (Lean.Expr.bvar 6)
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `RingHom.instFunLike [Lean.Level.param `u_1, Lean.Level.param `u_2])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_1])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 4)))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_2])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.bvar 3))))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Algebra.algebraMap [Lean.Level.param `u_1, Lean.Level.param `u_2])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 4)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.bvar 3))))
                      (Lean.Expr.bvar 2)))))
              (Lean.BinderInfo.instImplicit))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`PrimeSpectrum.comap_surjective_iff_injective_of_finite, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_1)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_2)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 1741335430) "_hygCtx") "_hyg") 4)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_1]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 1741335430) "_hygCtx") "_hyg") 7)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_2]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 1741335430) "_hygCtx") "_hyg") 10)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Algebra [Lean.Level.param `u_1, Lean.Level.param `u_2])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 1741335430) "_hygCtx") "_hyg") 14)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Module.Flat [Lean.Level.param `u_1, Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 2)))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.forallE
              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 1741335430) "_hygCtx") "_hyg") 18)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Module.Finite [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2)))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2))))
                  (Lean.Expr.bvar 1)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Iff [])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const
                          `Function.Surjective
                          [Lean.Level.succ (Lean.Level.param `u_2), Lean.Level.succ (Lean.Level.param `u_1)])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_2]) (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.bvar 3))))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1]) (Lean.Expr.bvar 6))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.bvar 4))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `PrimeSpectrum.comap [Lean.Level.param `u_1, Lean.Level.param `u_2])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 4)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.bvar 3)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Algebra.algebraMap [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 4)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.bvar 3))))
                        (Lean.Expr.bvar 2)))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `Function.Injective
                        [Lean.Level.succ (Lean.Level.param `u_1), Lean.Level.succ (Lean.Level.param `u_2)])
                      (Lean.Expr.bvar 6))
                    (Lean.Expr.bvar 5))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `DFunLike.coe
                              [Lean.Level.max
                                 (Lean.Level.succ (Lean.Level.param `u_1))
                                 (Lean.Level.succ (Lean.Level.param `u_2)),
                               Lean.Level.succ (Lean.Level.param `u_1),
                               Lean.Level.succ (Lean.Level.param `u_2)])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `RingHom [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_1])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 4)))))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 5))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.bvar 3))))))
                          (Lean.Expr.bvar 6))
                        (Lean.Expr.lam
                          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                          (Lean.Expr.bvar 6)
                          (Lean.Expr.bvar 6)
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `RingHom.instFunLike [Lean.Level.param `u_1, Lean.Level.param `u_2])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_1])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 4)))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_2])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.bvar 3))))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Algebra.algebraMap [Lean.Level.param `u_1, Lean.Level.param `u_2])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 4)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.bvar 3))))
                      (Lean.Expr.bvar 2)))))
              (Lean.BinderInfo.instImplicit))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_1)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_2)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2181739404) "_hygCtx") "_hyg") 4)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_1]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2181739404) "_hygCtx") "_hyg") 7)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_2]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2181739404) "_hygCtx") "_hyg") 10)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Algebra [Lean.Level.param `u_1, Lean.Level.param `u_2])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2181739404) "_hygCtx") "_hyg") 14)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Module.Flat [Lean.Level.param `u_1, Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 2)))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.forallE
              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2181739404) "_hygCtx") "_hyg") 18)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Module.Finite [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2)))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2))))
                  (Lean.Expr.bvar 1)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Iff [])
                  (Lean.Expr.forallE
                    `p
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1]) (Lean.Expr.bvar 6))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 6))
                        (Lean.Expr.bvar 4)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                          (Lean.Expr.const `instLTNat []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                            (Lean.Expr.lit (Lean.Literal.natVal 0)))
                          (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 0)))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Module.rankAtStalk [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Ring.toAddCommGroup [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toRing [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 4))))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 5)))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 4))))
                            (Lean.Expr.bvar 3)))
                        (Lean.Expr.bvar 0)))
                    (Lean.BinderInfo.default)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `Function.Surjective
                        [Lean.Level.succ (Lean.Level.param `u_2), Lean.Level.succ (Lean.Level.param `u_1)])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_2]) (Lean.Expr.bvar 5))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.bvar 3))))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1]) (Lean.Expr.bvar 6))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 6))
                        (Lean.Expr.bvar 4))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `PrimeSpectrum.comap [Lean.Level.param `u_1, Lean.Level.param `u_2])
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.bvar 4)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Algebra.algebraMap [Lean.Level.param `u_1, Lean.Level.param `u_2])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 4)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.bvar 3))))
                      (Lean.Expr.bvar 2)))))
              (Lean.BinderInfo.instImplicit))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_1)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_2)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2897022493) "_hygCtx") "_hyg") 4)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_1]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2897022493) "_hygCtx") "_hyg") 7)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_2]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2897022493) "_hygCtx") "_hyg") 10)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Algebra [Lean.Level.param `u_1, Lean.Level.param `u_2])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2897022493) "_hygCtx") "_hyg") 14)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Module.Flat [Lean.Level.param `u_1, Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 2)))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.forallE
              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2897022493) "_hygCtx") "_hyg") 18)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Module.Finite [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2)))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2))))
                  (Lean.Expr.bvar 1)))
              (Lean.Expr.forallE
                `p
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1]) (Lean.Expr.bvar 6))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                      (Lean.Expr.bvar 6))
                    (Lean.Expr.bvar 4)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Iff [])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                          (Lean.Expr.const `instLTNat []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                            (Lean.Expr.lit (Lean.Literal.natVal 0)))
                          (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 0)))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Module.rankAtStalk [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Ring.toAddCommGroup [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toRing [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 4))))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 5)))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 4))))
                            (Lean.Expr.bvar 3)))
                        (Lean.Expr.bvar 0))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Membership.mem [Lean.Level.param `u_1, Lean.Level.param `u_1])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.bvar 5))))
                          (Lean.Expr.app
                            (Lean.Expr.const `Set [Lean.Level.param `u_1])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.bvar 5)))))
                        (Lean.Expr.app
                          (Lean.Expr.const `Set.instMembership [Lean.Level.param `u_1])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1]) (Lean.Expr.bvar 7))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.bvar 5)))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `Set.range
                              [Lean.Level.param `u_1, Lean.Level.succ (Lean.Level.param `u_2)])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.bvar 5))))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_2]) (Lean.Expr.bvar 6))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 4))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `PrimeSpectrum.comap [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.bvar 5)))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 4)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Algebra.algebraMap [Lean.Level.param `u_1, Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 5)))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 4))))
                            (Lean.Expr.bvar 3)))))
                    (Lean.Expr.bvar 0)))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.instImplicit))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`RingHom.finrank, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_3)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_4)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 441184222) "_hygCtx") "_hyg") 16)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_3]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 441184222) "_hygCtx") "_hyg") 19)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_4]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          `f
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `RingHom [Lean.Level.param `u_3, Lean.Level.param `u_4])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_3])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_3]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.bvar 1)))))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_4]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4]) (Lean.Expr.bvar 2))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4]) (Lean.Expr.bvar 2))
                  (Lean.Expr.bvar 0)))))
          (Lean.Expr.forallE
            `x
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_3]) (Lean.Expr.bvar 4))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3]) (Lean.Expr.bvar 4))
                (Lean.Expr.bvar 2)))
            (Lean.Expr.const `Nat [])
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`RingHom.finrank.eq_1, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_3)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_4)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 441184222) "_hygCtx") "_hyg") 16)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_3]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 441184222) "_hygCtx") "_hyg") 19)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_4]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          `f
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `RingHom [Lean.Level.param `u_3, Lean.Level.param `u_4])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_3])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_3]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.bvar 1)))))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_4]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4]) (Lean.Expr.bvar 2))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4]) (Lean.Expr.bvar 2))
                  (Lean.Expr.bvar 0)))))
          (Lean.Expr.forallE
            `x
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_3]) (Lean.Expr.bvar 4))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3]) (Lean.Expr.bvar 4))
                (Lean.Expr.bvar 2)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `RingHom.finrank [Lean.Level.param `u_3, Lean.Level.param `u_4])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 2))
                    (Lean.Expr.bvar 1))
                  (Lean.Expr.bvar 0)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Module.rankAtStalk [Lean.Level.param `u_3, Lean.Level.param `u_4])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Ring.toAddCommGroup [Lean.Level.param `u_4]) (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `CommRing.toRing [Lean.Level.param `u_4]) (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_3, Lean.Level.param `u_4])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.bvar 3)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                            (Lean.Expr.bvar 4))
                          (Lean.Expr.bvar 2))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `RingHom.toAlgebra [Lean.Level.param `u_3, Lean.Level.param `u_4])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.bvar 4))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.bvar 3)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                            (Lean.Expr.bvar 4))
                          (Lean.Expr.bvar 2)))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.bvar 0)))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`RingHom.finrank_algebraMap, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_1)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_2)))
    (Lean.Expr.forallE
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2909478803) "_hygCtx") "_hyg") 4)
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_1]) (Lean.Expr.bvar 1))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2909478803) "_hygCtx") "_hyg") 7)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_2]) (Lean.Expr.bvar 1))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 2909478803) "_hygCtx") "_hyg") 10)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Algebra [Lean.Level.param `u_1, Lean.Level.param `u_2])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2]) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.param `u_1)])
                (Lean.Expr.forallE
                  `x
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_1]) (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2)))
                  (Lean.Expr.const `Nat [])
                  (Lean.BinderInfo.default)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `RingHom.finrank [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.bvar 2))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Algebra.algebraMap [Lean.Level.param `u_1, Lean.Level.param `u_2])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                          (Lean.Expr.bvar 3))
                        (Lean.Expr.bvar 1))))
                  (Lean.Expr.bvar 0))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Module.rankAtStalk [Lean.Level.param `u_1, Lean.Level.param `u_2])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.bvar 2))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Ring.toAddCommGroup [Lean.Level.param `u_2]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `CommRing.toRing [Lean.Level.param `u_2]) (Lean.Expr.bvar 3))
                    (Lean.Expr.bvar 1))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Algebra.toModule [Lean.Level.param `u_1, Lean.Level.param `u_2])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_1])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_2])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_2])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.bvar 0))))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`RingHom.finrank_comp_left_of_bijective, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_3)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_4)))
    (Lean.Expr.forallE
      `T
      (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_5)))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 247459168) "_hygCtx") "_hyg") 17)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_3]) (Lean.Expr.bvar 2))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 247459168) "_hygCtx") "_hyg") 20)
          (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_4]) (Lean.Expr.bvar 2))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 247459168) "_hygCtx") "_hyg") 23)
            (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_5]) (Lean.Expr.bvar 2))
            (Lean.Expr.forallE
              `f
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `RingHom [Lean.Level.param `u_3, Lean.Level.param `u_4])
                      (Lean.Expr.bvar 5))
                    (Lean.Expr.bvar 4))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_3])
                      (Lean.Expr.bvar 5))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_3])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 2)))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_4])
                    (Lean.Expr.bvar 4))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 1)))))
              (Lean.Expr.forallE
                `g
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `RingHom [Lean.Level.param `u_4, Lean.Level.param `u_5])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_4])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.bvar 2)))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_5])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_5])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_5])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 1)))))
                (Lean.Expr.forallE
                  `hf
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const
                          `Function.Bijective
                          [Lean.Level.succ (Lean.Level.param `u_4), Lean.Level.succ (Lean.Level.param `u_5)])
                        (Lean.Expr.bvar 6))
                      (Lean.Expr.bvar 5))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `DFunLike.coe
                                [Lean.Level.max
                                   (Lean.Level.succ (Lean.Level.param `u_4))
                                   (Lean.Level.succ (Lean.Level.param `u_5)),
                                 Lean.Level.succ (Lean.Level.param `u_4),
                                 Lean.Level.succ (Lean.Level.param `u_5)])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `RingHom [Lean.Level.param `u_4, Lean.Level.param `u_5])
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.bvar 5))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_4])
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                                          (Lean.Expr.bvar 6))
                                        (Lean.Expr.bvar 3)))))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_5])
                                    (Lean.Expr.bvar 5))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_5])
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_5])
                                        (Lean.Expr.bvar 5))
                                      (Lean.Expr.bvar 2))))))
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.lam
                            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                            (Lean.Expr.bvar 6)
                            (Lean.Expr.bvar 6)
                            (Lean.BinderInfo.default)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `RingHom.instFunLike [Lean.Level.param `u_4, Lean.Level.param `u_5])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_4])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.bvar 3)))))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_5])
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_5])
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_5])
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.bvar 2))))))
                      (Lean.Expr.bvar 0)))
                  (Lean.Expr.forallE
                    `h1
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `RingHom.Finite [Lean.Level.param `u_3, Lean.Level.param `u_4])
                              (Lean.Expr.bvar 8))
                            (Lean.Expr.bvar 7))
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 2))
                    (Lean.Expr.forallE
                      `h2
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `RingHom.Flat [Lean.Level.param `u_3, Lean.Level.param `u_4])
                                (Lean.Expr.bvar 9))
                              (Lean.Expr.bvar 8))
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.forallE
                        `x
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_3]) (Lean.Expr.bvar 10))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                              (Lean.Expr.bvar 10))
                            (Lean.Expr.bvar 7)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                              (Lean.Expr.const `Nat []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `RingHom.finrank
                                          [Lean.Level.param `u_3, Lean.Level.param `u_5])
                                        (Lean.Expr.bvar 11))
                                      (Lean.Expr.bvar 9))
                                    (Lean.Expr.bvar 8))
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `RingHom.comp
                                                  [Lean.Level.param `u_3, Lean.Level.param `u_4, Lean.Level.param `u_5])
                                                (Lean.Expr.bvar 11))
                                              (Lean.Expr.bvar 10))
                                            (Lean.Expr.bvar 9))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_3])
                                              (Lean.Expr.bvar 11))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_3])
                                                (Lean.Expr.bvar 11))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                                  (Lean.Expr.bvar 11))
                                                (Lean.Expr.bvar 8)))))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_4])
                                            (Lean.Expr.bvar 10))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                                              (Lean.Expr.bvar 10))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                                                (Lean.Expr.bvar 10))
                                              (Lean.Expr.bvar 7)))))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_5])
                                          (Lean.Expr.bvar 9))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_5])
                                            (Lean.Expr.bvar 9))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_5])
                                              (Lean.Expr.bvar 9))
                                            (Lean.Expr.bvar 6)))))
                                    (Lean.Expr.bvar 4))
                                  (Lean.Expr.bvar 5)))
                              (Lean.Expr.bvar 0)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `RingHom.finrank [Lean.Level.param `u_3, Lean.Level.param `u_4])
                                      (Lean.Expr.bvar 11))
                                    (Lean.Expr.bvar 10))
                                  (Lean.Expr.bvar 8))
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.bvar 0)))
                        (Lean.BinderInfo.default))
                      (Lean.BinderInfo.default))
                    (Lean.BinderInfo.default))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.implicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit))),
  (`RingHom.finrank_comp_right_of_bijective, (Lean.Expr.forallE
  `R
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_3)))
  (Lean.Expr.forallE
    `S
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_4)))
    (Lean.Expr.forallE
      `T
      (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_5)))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 1380943129) "_hygCtx") "_hyg") 17)
        (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_3]) (Lean.Expr.bvar 2))
        (Lean.Expr.forallE
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 1380943129) "_hygCtx") "_hyg") 20)
          (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_4]) (Lean.Expr.bvar 2))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».ThetaStdRingFlatRank 1380943129) "_hygCtx") "_hyg") 23)
            (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u_5]) (Lean.Expr.bvar 2))
            (Lean.Expr.forallE
              `f
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `RingHom [Lean.Level.param `u_3, Lean.Level.param `u_4])
                      (Lean.Expr.bvar 5))
                    (Lean.Expr.bvar 4))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_3])
                      (Lean.Expr.bvar 5))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_3])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 2)))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_4])
                    (Lean.Expr.bvar 4))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 1)))))
              (Lean.Expr.forallE
                `g
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `RingHom [Lean.Level.param `u_4, Lean.Level.param `u_5])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_4])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.bvar 2)))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_5])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_5])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_5])
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 1)))))
                (Lean.Expr.forallE
                  `hg
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const
                          `Function.Bijective
                          [Lean.Level.succ (Lean.Level.param `u_3), Lean.Level.succ (Lean.Level.param `u_4)])
                        (Lean.Expr.bvar 7))
                      (Lean.Expr.bvar 6))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `DFunLike.coe
                                [Lean.Level.max
                                   (Lean.Level.succ (Lean.Level.param `u_3))
                                   (Lean.Level.succ (Lean.Level.param `u_4)),
                                 Lean.Level.succ (Lean.Level.param `u_3),
                                 Lean.Level.succ (Lean.Level.param `u_4)])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `RingHom [Lean.Level.param `u_3, Lean.Level.param `u_4])
                                      (Lean.Expr.bvar 7))
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_3])
                                      (Lean.Expr.bvar 7))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_3])
                                        (Lean.Expr.bvar 7))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                          (Lean.Expr.bvar 7))
                                        (Lean.Expr.bvar 4)))))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_4])
                                    (Lean.Expr.bvar 6))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 3))))))
                            (Lean.Expr.bvar 7))
                          (Lean.Expr.lam
                            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                            (Lean.Expr.bvar 7)
                            (Lean.Expr.bvar 7)
                            (Lean.BinderInfo.default)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `RingHom.instFunLike [Lean.Level.param `u_3, Lean.Level.param `u_4])
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_3])
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_3])
                                  (Lean.Expr.bvar 7))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                    (Lean.Expr.bvar 7))
                                  (Lean.Expr.bvar 4)))))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_4])
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 3))))))
                      (Lean.Expr.bvar 1)))
                  (Lean.Expr.forallE
                    `h1
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `RingHom.Finite [Lean.Level.param `u_4, Lean.Level.param `u_5])
                              (Lean.Expr.bvar 7))
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 1))
                    (Lean.Expr.forallE
                      `h2
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `RingHom.Flat [Lean.Level.param `u_4, Lean.Level.param `u_5])
                                (Lean.Expr.bvar 8))
                              (Lean.Expr.bvar 7))
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.bvar 4))
                        (Lean.Expr.bvar 2))
                      (Lean.Expr.forallE
                        `y
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_3]) (Lean.Expr.bvar 10))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                              (Lean.Expr.bvar 10))
                            (Lean.Expr.bvar 7)))
                        (Lean.Expr.forallE
                          `x
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_4]) (Lean.Expr.bvar 10))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                                (Lean.Expr.bvar 10))
                              (Lean.Expr.bvar 7)))
                          (Lean.Expr.forallE
                            `hy
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.param `u_3)])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `PrimeSpectrum [Lean.Level.param `u_3])
                                      (Lean.Expr.bvar 12))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                        (Lean.Expr.bvar 12))
                                      (Lean.Expr.bvar 9))))
                                (Lean.Expr.bvar 1))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `PrimeSpectrum.comap
                                            [Lean.Level.param `u_3, Lean.Level.param `u_4])
                                          (Lean.Expr.bvar 12))
                                        (Lean.Expr.bvar 11))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                          (Lean.Expr.bvar 12))
                                        (Lean.Expr.bvar 9)))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                                        (Lean.Expr.bvar 11))
                                      (Lean.Expr.bvar 8)))
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 0)))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                                  (Lean.Expr.const `Nat []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `RingHom.finrank
                                              [Lean.Level.param `u_3, Lean.Level.param `u_5])
                                            (Lean.Expr.bvar 13))
                                          (Lean.Expr.bvar 11))
                                        (Lean.Expr.bvar 10))
                                      (Lean.Expr.bvar 8))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `RingHom.comp
                                                      [Lean.Level.param `u_3,
                                                       Lean.Level.param `u_4,
                                                       Lean.Level.param `u_5])
                                                    (Lean.Expr.bvar 13))
                                                  (Lean.Expr.bvar 12))
                                                (Lean.Expr.bvar 11))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_3])
                                                  (Lean.Expr.bvar 13))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_3])
                                                    (Lean.Expr.bvar 13))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_3])
                                                      (Lean.Expr.bvar 13))
                                                    (Lean.Expr.bvar 10)))))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_4])
                                                (Lean.Expr.bvar 12))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_4])
                                                  (Lean.Expr.bvar 12))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_4])
                                                    (Lean.Expr.bvar 12))
                                                  (Lean.Expr.bvar 9)))))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.param `u_5])
                                              (Lean.Expr.bvar 11))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u_5])
                                                (Lean.Expr.bvar 11))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u_5])
                                                  (Lean.Expr.bvar 11))
                                                (Lean.Expr.bvar 8)))))
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 7)))
                                  (Lean.Expr.bvar 2)))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `RingHom.finrank
                                            [Lean.Level.param `u_4, Lean.Level.param `u_5])
                                          (Lean.Expr.bvar 12))
                                        (Lean.Expr.bvar 11))
                                      (Lean.Expr.bvar 9))
                                    (Lean.Expr.bvar 8))
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 1)))
                            (Lean.BinderInfo.default))
                          (Lean.BinderInfo.default))
                        (Lean.BinderInfo.default))
                      (Lean.BinderInfo.default))
                    (Lean.BinderInfo.default))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.instImplicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.implicit))
    (Lean.BinderInfo.implicit))
  (Lean.BinderInfo.implicit)))
  ]
  for i in [:originals.size] do
    let (n, originalType) := originals[i]!
    logInfo m!"EXACT_RECONSTRUCTED_TYPE_BEGIN {n}
{reprStr originalType}
EXACT_RECONSTRUCTED_TYPE_END {n}"
    let some canonical := (← getEnv).find? n | throwError "Missing canonical interface {n}"
    let equality ← liftTermElabM do Meta.mkEq originalType canonical.type
    let refl ← liftTermElabM do Meta.mkEqRefl originalType
    let certificate := Name.str `FourCorner.ThetaSurvivingActualJacobians.ExactInterface ("type_" ++ toString i)
    liftCoreM <| addDecl <| .thmDecl {
      name := certificate
      levelParams := canonical.levelParams
      type := equality
      value := refl
    }
    logInfo m!"EXACT_TYPE_KERNEL_CERTIFICATE {certificate} {n}"
