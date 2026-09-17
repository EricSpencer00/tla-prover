;; Proof obligation:
;;	ASSUME \A CONSTANT_S_ : \E CONSTANT_x_ : CONSTANT_x_ \notin CONSTANT_S_ 
;;	PROVE  \A CONSTANT_N_ \in Nat :
;;	          \E CONSTANT_n_ \in Nat :
;;	             CONSTANT_n_ > CONSTANT_N_
;;	             /\ (\E CONSTANT_i_ \in [{0, 1, 2, 3, 4, 5} -> Nat] :
;;	                    CONSTANT_n_
;;	                    = CONSTANT_i_[0] * CONSTANT_i_[0]
;;	                      + CONSTANT_i_[1] * CONSTANT_i_[1]
;;	                    /\ CONSTANT_n_ + 1
;;	                       = CONSTANT_i_[2] * CONSTANT_i_[2]
;;	                         + CONSTANT_i_[3] * CONSTANT_i_[3]
;;	                    /\ CONSTANT_n_ + 2
;;	                       = CONSTANT_i_[4] * CONSTANT_i_[4]
;;	                         + CONSTANT_i_[5] * CONSTANT_i_[5])
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./exercise_2000_a2.tla", line 11, characters 55-56

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Cast__Int (Int) Idv)

(declare-fun smt__TLA____FunApp (Idv Idv) Idv)

(declare-fun smt__TLA____FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA____FunIsafcn (Idv) Bool)

(declare-fun smt__TLA____FunSet (Idv Idv) Idv)

(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)

(declare-fun smt__TLA____IntPlus (Idv Idv) Idv)

(declare-fun smt__TLA____IntSet () Idv)

(declare-fun smt__TLA____IntTimes (Idv Idv) Idv)

(declare-fun smt__TLA____Mem (Idv Idv) Bool)

(declare-fun smt__TLA____NatSet () Idv)

(declare-fun smt__TLA____Proj__Int (Idv) Int)

(declare-fun smt__TLA____SetEnum__6 (Idv Idv Idv Idv Idv Idv) Idv)

(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)

;; Axiom: SetExt
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=>
          (forall ((smt__z Idv))
            (= (smt__TLA____Mem smt__z smt__x)
              (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y))
        :pattern ((smt__TLA____SetExtTrigger smt__x smt__y))))
    :named |SetExt|))

;; Axiom: NatSetDef
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (= (smt__TLA____Mem smt__x smt__TLA____NatSet)
          (and (smt__TLA____Mem smt__x smt__TLA____IntSet)
            (smt__TLA____IntLteq (smt__TLA____Cast__Int 0) smt__x)))
        :pattern ((smt__TLA____Mem smt__x smt__TLA____NatSet))))
    :named |NatSetDef|))

;; Axiom: FunExt
(assert
  (!
    (forall ((smt__f Idv) (smt__g Idv))
      (!
        (=>
          (and (smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g)
            (= (smt__TLA____FunDom smt__f) (smt__TLA____FunDom smt__g))
            (forall ((smt__x Idv))
              (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom smt__f))
                (= (smt__TLA____FunApp smt__f smt__x)
                  (smt__TLA____FunApp smt__g smt__x))))) (= smt__f smt__g))
        :pattern ((smt__TLA____FunIsafcn smt__f)
                   (smt__TLA____FunIsafcn smt__g)))) :named |FunExt|))

; omitted fact (second-order)

;; Axiom: FunSetIntro
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (and (smt__TLA____FunIsafcn smt__f)
            (= (smt__TLA____FunDom smt__f) smt__a)
            (forall ((smt__x Idv))
              (=> (smt__TLA____Mem smt__x smt__a)
                (smt__TLA____Mem (smt__TLA____FunApp smt__f smt__x) smt__b))))
          (smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b)))
        :pattern ((smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b)))))
    :named |FunSetIntro|))

;; Axiom: FunSetElim1
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=> (smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b))
          (and (smt__TLA____FunIsafcn smt__f)
            (= (smt__TLA____FunDom smt__f) smt__a)))
        :pattern ((smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b)))))
    :named |FunSetElim1|))

;; Axiom: FunSetElim2
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv) (smt__x Idv))
      (!
        (=>
          (and (smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b))
            (smt__TLA____Mem smt__x smt__a))
          (smt__TLA____Mem (smt__TLA____FunApp smt__f smt__x) smt__b))
        :pattern ((smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b))
                   (smt__TLA____Mem smt__x smt__a))
        :pattern ((smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b))
                   (smt__TLA____FunApp smt__f smt__x)))) :named |FunSetElim2|))

; omitted fact (second-order)

; omitted fact (second-order)

; omitted fact (second-order)

;; Axiom: EnumDefIntro 6
(assert
  (!
    (forall
      ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__a4 Idv) (smt__a5 Idv)
        (smt__a6 Idv))
      (!
        (and
          (smt__TLA____Mem smt__a1
            (smt__TLA____SetEnum__6 smt__a1 smt__a2 smt__a3 smt__a4 smt__a5
              smt__a6))
          (smt__TLA____Mem smt__a2
            (smt__TLA____SetEnum__6 smt__a1 smt__a2 smt__a3 smt__a4 smt__a5
              smt__a6))
          (smt__TLA____Mem smt__a3
            (smt__TLA____SetEnum__6 smt__a1 smt__a2 smt__a3 smt__a4 smt__a5
              smt__a6))
          (smt__TLA____Mem smt__a4
            (smt__TLA____SetEnum__6 smt__a1 smt__a2 smt__a3 smt__a4 smt__a5
              smt__a6))
          (smt__TLA____Mem smt__a5
            (smt__TLA____SetEnum__6 smt__a1 smt__a2 smt__a3 smt__a4 smt__a5
              smt__a6))
          (smt__TLA____Mem smt__a6
            (smt__TLA____SetEnum__6 smt__a1 smt__a2 smt__a3 smt__a4 smt__a5
              smt__a6)))
        :pattern ((smt__TLA____SetEnum__6 smt__a1 smt__a2 smt__a3 smt__a4
                    smt__a5 smt__a6)))) :named |EnumDefIntro 6|))

;; Axiom: EnumDefElim 6
(assert
  (!
    (forall
      ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__a4 Idv) (smt__a5 Idv)
        (smt__a6 Idv) (smt__x Idv))
      (!
        (=>
          (smt__TLA____Mem smt__x
            (smt__TLA____SetEnum__6 smt__a1 smt__a2 smt__a3 smt__a4 smt__a5
              smt__a6))
          (or (= smt__x smt__a1) (= smt__x smt__a2) (= smt__x smt__a3)
            (= smt__x smt__a4) (= smt__x smt__a5) (= smt__x smt__a6)))
        :pattern ((smt__TLA____Mem smt__x
                    (smt__TLA____SetEnum__6 smt__a1 smt__a2 smt__a3 smt__a4
                      smt__a5 smt__a6))))) :named |EnumDefElim 6|))

;; Axiom: CastInjAlt Int
(assert
  (!
    (forall ((smt__x Int))
      (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x)))
        :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))

;; Axiom: TypeGuardIntro Int
(assert
  (!
    (forall ((smt__z Int))
      (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet)
        :pattern ((smt__TLA____Cast__Int smt__z))))
    :named |TypeGuardIntro Int|))

;; Axiom: TypeGuardElim Int
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (=> (smt__TLA____Mem smt__x smt__TLA____IntSet)
          (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x))))
        :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet))))
    :named |TypeGuardElim Int|))

;; Axiom: Typing TIntPlus
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (smt__TLA____IntPlus (smt__TLA____Cast__Int smt__x1)
            (smt__TLA____Cast__Int smt__x2))
          (smt__TLA____Cast__Int (+ smt__x1 smt__x2)))
        :pattern ((smt__TLA____IntPlus (smt__TLA____Cast__Int smt__x1)
                    (smt__TLA____Cast__Int smt__x2)))))
    :named |Typing TIntPlus|))

;; Axiom: Typing TIntTimes
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (smt__TLA____IntTimes (smt__TLA____Cast__Int smt__x1)
            (smt__TLA____Cast__Int smt__x2))
          (smt__TLA____Cast__Int (* smt__x1 smt__x2)))
        :pattern ((smt__TLA____IntTimes (smt__TLA____Cast__Int smt__x1)
                    (smt__TLA____Cast__Int smt__x2)))))
    :named |Typing TIntTimes|))

;; Axiom: Typing TIntLteq
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1)
            (smt__TLA____Cast__Int smt__x2)) (<= smt__x1 smt__x2))
        :pattern ((smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1)
                    (smt__TLA____Cast__Int smt__x2)))))
    :named |Typing TIntLteq|))

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_EnabledWrapper_' (second-order)

; omitted declaration of 'CONSTANT_CdotWrapper_' (second-order)

(assert
  (forall ((smt__CONSTANT__S__ Idv))
    (exists ((smt__CONSTANT__x__ Idv))
      (not (smt__TLA____Mem smt__CONSTANT__x__ smt__CONSTANT__S__)))))

;; Goal
(assert
  (!
    (not
      (forall ((smt__CONSTANT__N__ Idv))
        (=> (smt__TLA____Mem smt__CONSTANT__N__ smt__TLA____NatSet)
          (exists ((smt__CONSTANT__n__ Idv))
            (and (smt__TLA____Mem smt__CONSTANT__n__ smt__TLA____NatSet)
              (and
                (and
                  (smt__TLA____IntLteq smt__CONSTANT__N__ smt__CONSTANT__n__)
                  (distinct smt__CONSTANT__N__ smt__CONSTANT__n__))
                (exists ((smt__CONSTANT__i__ Idv))
                  (and
                    (smt__TLA____Mem smt__CONSTANT__i__
                      (smt__TLA____FunSet
                        (smt__TLA____SetEnum__6 (smt__TLA____Cast__Int 0)
                          (smt__TLA____Cast__Int 1) (smt__TLA____Cast__Int 2)
                          (smt__TLA____Cast__Int 3) (smt__TLA____Cast__Int 4)
                          (smt__TLA____Cast__Int 5)) smt__TLA____NatSet))
                    (and
                      (and
                        (= smt__CONSTANT__n__
                          (smt__TLA____IntPlus
                            (smt__TLA____IntTimes
                              (smt__TLA____FunApp smt__CONSTANT__i__
                                (smt__TLA____Cast__Int 0))
                              (smt__TLA____FunApp smt__CONSTANT__i__
                                (smt__TLA____Cast__Int 0)))
                            (smt__TLA____IntTimes
                              (smt__TLA____FunApp smt__CONSTANT__i__
                                (smt__TLA____Cast__Int 1))
                              (smt__TLA____FunApp smt__CONSTANT__i__
                                (smt__TLA____Cast__Int 1)))))
                        (=
                          (smt__TLA____IntPlus smt__CONSTANT__n__
                            (smt__TLA____Cast__Int 1))
                          (smt__TLA____IntPlus
                            (smt__TLA____IntTimes
                              (smt__TLA____FunApp smt__CONSTANT__i__
                                (smt__TLA____Cast__Int 2))
                              (smt__TLA____FunApp smt__CONSTANT__i__
                                (smt__TLA____Cast__Int 2)))
                            (smt__TLA____IntTimes
                              (smt__TLA____FunApp smt__CONSTANT__i__
                                (smt__TLA____Cast__Int 3))
                              (smt__TLA____FunApp smt__CONSTANT__i__
                                (smt__TLA____Cast__Int 3))))))
                      (=
                        (smt__TLA____IntPlus smt__CONSTANT__n__
                          (smt__TLA____Cast__Int 2))
                        (smt__TLA____IntPlus
                          (smt__TLA____IntTimes
                            (smt__TLA____FunApp smt__CONSTANT__i__
                              (smt__TLA____Cast__Int 4))
                            (smt__TLA____FunApp smt__CONSTANT__i__
                              (smt__TLA____Cast__Int 4)))
                          (smt__TLA____IntTimes
                            (smt__TLA____FunApp smt__CONSTANT__i__
                              (smt__TLA____Cast__Int 5))
                            (smt__TLA____FunApp smt__CONSTANT__i__
                              (smt__TLA____Cast__Int 5))))))))))))))
    :named |Goal|))

(check-sat)
(exit)
