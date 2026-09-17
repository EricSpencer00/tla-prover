;; Proof obligation:
;;	ASSUME \A CONSTANT_S_, CONSTANT_T_ :
;;	          (\A CONSTANT_x_ :
;;	              CONSTANT_x_ \in CONSTANT_S_ <=> CONSTANT_x_ \in CONSTANT_T_)
;;	          => CONSTANT_S_ = CONSTANT_T_ ,
;;	       \A CONSTANT_S_ : \E CONSTANT_x_ : CONSTANT_x_ \notin CONSTANT_S_ 
;;	PROVE  \A CONSTANT_x_ \in [Nat -> Int] :
;;	          CONSTANT_x_[1] = 211 /\ CONSTANT_x_[2] = 375
;;	          /\ CONSTANT_x_[3] = 420 /\ CONSTANT_x_[4] = 523
;;	          /\ (\A CONSTANT_n_ \in Nat :
;;	                 CONSTANT_n_ >= 5
;;	                 => CONSTANT_x_[CONSTANT_n_]
;;	                    = CONSTANT_x_[CONSTANT_n_ - 1]
;;	                      - CONSTANT_x_[CONSTANT_n_ - 2]
;;	                      + CONSTANT_x_[CONSTANT_n_ - 3]
;;	                        - CONSTANT_x_[CONSTANT_n_ - 4])
;;	          => CONSTANT_x_[531] + CONSTANT_x_[753] + CONSTANT_x_[975] = 898
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./aimeII_2001_p3.tla", line 6, characters 204-205

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

(declare-fun smt__TLA____IntMinus (Idv Idv) Idv)

(declare-fun smt__TLA____IntPlus (Idv Idv) Idv)

(declare-fun smt__TLA____IntSet () Idv)

(declare-fun smt__TLA____Mem (Idv Idv) Bool)

(declare-fun smt__TLA____NatSet () Idv)

(declare-fun smt__TLA____Proj__Int (Idv) Int)

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

;; Axiom: Typing TIntMinus
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (smt__TLA____IntMinus (smt__TLA____Cast__Int smt__x1)
            (smt__TLA____Cast__Int smt__x2))
          (smt__TLA____Cast__Int (- smt__x1 smt__x2)))
        :pattern ((smt__TLA____IntMinus (smt__TLA____Cast__Int smt__x1)
                    (smt__TLA____Cast__Int smt__x2)))))
    :named |Typing TIntMinus|))

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
  (forall ((smt__CONSTANT__S__ Idv) (smt__CONSTANT__T__ Idv))
    (=>
      (forall ((smt__CONSTANT__x__ Idv))
        (= (smt__TLA____Mem smt__CONSTANT__x__ smt__CONSTANT__S__)
          (smt__TLA____Mem smt__CONSTANT__x__ smt__CONSTANT__T__)))
      (= smt__CONSTANT__S__ smt__CONSTANT__T__))))

(assert
  (forall ((smt__CONSTANT__S__ Idv))
    (exists ((smt__CONSTANT__x__ Idv))
      (not (smt__TLA____Mem smt__CONSTANT__x__ smt__CONSTANT__S__)))))

;; Goal
(assert
  (!
    (not
      (forall ((smt__CONSTANT__x__ Idv))
        (=>
          (smt__TLA____Mem smt__CONSTANT__x__
            (smt__TLA____FunSet smt__TLA____NatSet smt__TLA____IntSet))
          (=>
            (and
              (and
                (and
                  (and
                    (=
                      (smt__TLA____FunApp smt__CONSTANT__x__
                        (smt__TLA____Cast__Int 1))
                      (smt__TLA____Cast__Int 211))
                    (=
                      (smt__TLA____FunApp smt__CONSTANT__x__
                        (smt__TLA____Cast__Int 2))
                      (smt__TLA____Cast__Int 375)))
                  (=
                    (smt__TLA____FunApp smt__CONSTANT__x__
                      (smt__TLA____Cast__Int 3)) (smt__TLA____Cast__Int 420)))
                (=
                  (smt__TLA____FunApp smt__CONSTANT__x__
                    (smt__TLA____Cast__Int 4)) (smt__TLA____Cast__Int 523)))
              (forall ((smt__CONSTANT__n__ Idv))
                (=> (smt__TLA____Mem smt__CONSTANT__n__ smt__TLA____NatSet)
                  (=>
                    (smt__TLA____IntLteq (smt__TLA____Cast__Int 5)
                      smt__CONSTANT__n__)
                    (=
                      (smt__TLA____FunApp smt__CONSTANT__x__
                        smt__CONSTANT__n__)
                      (smt__TLA____IntPlus
                        (smt__TLA____IntMinus
                          (smt__TLA____FunApp smt__CONSTANT__x__
                            (smt__TLA____IntMinus smt__CONSTANT__n__
                              (smt__TLA____Cast__Int 1)))
                          (smt__TLA____FunApp smt__CONSTANT__x__
                            (smt__TLA____IntMinus smt__CONSTANT__n__
                              (smt__TLA____Cast__Int 2))))
                        (smt__TLA____IntMinus
                          (smt__TLA____FunApp smt__CONSTANT__x__
                            (smt__TLA____IntMinus smt__CONSTANT__n__
                              (smt__TLA____Cast__Int 3)))
                          (smt__TLA____FunApp smt__CONSTANT__x__
                            (smt__TLA____IntMinus smt__CONSTANT__n__
                              (smt__TLA____Cast__Int 4))))))))))
            (=
              (smt__TLA____IntPlus
                (smt__TLA____IntPlus
                  (smt__TLA____FunApp smt__CONSTANT__x__
                    (smt__TLA____Cast__Int 531))
                  (smt__TLA____FunApp smt__CONSTANT__x__
                    (smt__TLA____Cast__Int 753)))
                (smt__TLA____FunApp smt__CONSTANT__x__
                  (smt__TLA____Cast__Int 975))) (smt__TLA____Cast__Int 898))))))
    :named |Goal|))

(check-sat)
(exit)
