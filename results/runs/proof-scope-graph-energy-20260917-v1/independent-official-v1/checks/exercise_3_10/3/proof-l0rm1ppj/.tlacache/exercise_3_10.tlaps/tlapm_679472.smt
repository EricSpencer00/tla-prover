;; Proof obligation:
;;	ASSUME CONSTANT_NatInductiveDefConclusion_(CONSTANT_factorial_, 1,
;;	                                           LAMBDA Unknown_v_, Unknown_n_ :
;;	                                             Unknown_n_ * Unknown_v_) ,
;;	       \A CONSTANT_n_ \in Nat :
;;	          CONSTANT_factorial_[CONSTANT_n_]
;;	          = (IF CONSTANT_n_ = 0
;;	               THEN 1
;;	               ELSE CONSTANT_n_ * CONSTANT_factorial_[CONSTANT_n_ - 1]) ,
;;	       ASSUME NEW CONSTANT CONSTANT_P_(_),
;;	              NEW CONSTANT CONSTANT_m_ \in Nat,
;;	              CONSTANT_P_(CONSTANT_m_) ,
;;	              \A CONSTANT_n_ \in 1..CONSTANT_m_ :
;;	                 CONSTANT_P_(CONSTANT_n_) => CONSTANT_P_(CONSTANT_n_ - 1) 
;;	       PROVE  CONSTANT_P_(0) 
;;	PROVE  \A CONSTANT_n_ \in Nat :
;;	          ~CONSTANT_IsPrime_(CONSTANT_n_) /\ CONSTANT_n_ # 4
;;	          => CONSTANT_factorial_[CONSTANT_n_ - 1] % CONSTANT_n_ = 0
;; TLA+ Proof Manager 80172c6
;; Proof obligation #7
;; Generated from file "./exercise_3_10.tla", line 22, characters 31-32

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Cast__Int (Int) Idv)

(declare-fun smt__TLA____FunApp (Idv Idv) Idv)

(declare-fun smt__TLA____FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA____FunIsafcn (Idv) Bool)

(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)

(declare-fun smt__TLA____IntMinus (Idv Idv) Idv)

(declare-fun smt__TLA____IntRange (Idv Idv) Idv)

(declare-fun smt__TLA____IntRemainder (Idv Idv) Idv)

(declare-fun smt__TLA____IntSet () Idv)

(declare-fun smt__TLA____IntTimes (Idv Idv) Idv)

(declare-fun smt__TLA____Mem (Idv Idv) Bool)

(declare-fun smt__TLA____NatSet () Idv)

(declare-fun smt__TLA____Proj__Int (Idv) Int)

(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLA____Tt__Idv () Idv)

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

;; Axiom: IntRangeDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (= (smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b))
          (and (smt__TLA____Mem smt__x smt__TLA____IntSet)
            (smt__TLA____IntLteq smt__a smt__x)
            (smt__TLA____IntLteq smt__x smt__b)))
        :pattern ((smt__TLA____Mem smt__x
                    (smt__TLA____IntRange smt__a smt__b)))))
    :named |IntRangeDef|))

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

;; Axiom: Typing TIntRemainder
(assert
  (!
    (forall ((smt__x Int) (smt__y Int))
      (!
        (=> (> smt__y 0)
          (=
            (smt__TLA____IntRemainder (smt__TLA____Cast__Int smt__x)
              (smt__TLA____Cast__Int smt__y))
            (smt__TLA____Cast__Int (mod smt__x smt__y))))
        :pattern ((smt__TLA____IntRemainder (smt__TLA____Cast__Int smt__x)
                    (smt__TLA____Cast__Int smt__y)))))
    :named |Typing TIntRemainder|))

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

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_NatInductiveDefHypothesis_' (second-order)

; omitted declaration of 'CONSTANT_NatInductiveDefConclusion_' (second-order)

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_FiniteNatInductiveDefHypothesis_' (second-order)

; omitted declaration of 'CONSTANT_FiniteNatInductiveDefConclusion_' (second-order)

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__CONSTANT__factorial__ () Idv)

; hidden fact

; hidden fact

(declare-fun smt__CONSTANT__IsPrime__ (Idv) Idv)

(declare-fun smt__CONSTANT__NatInductiveDefConclusion____flatnd__1 (Idv
  Idv) Idv)

(assert
  (=
    (smt__CONSTANT__NatInductiveDefConclusion____flatnd__1
      smt__CONSTANT__factorial__ (smt__TLA____Cast__Int 1))
    smt__TLA____Tt__Idv))

(assert
  (forall ((smt__CONSTANT__n__ Idv))
    (=> (smt__TLA____Mem smt__CONSTANT__n__ smt__TLA____NatSet)
      (= (smt__TLA____FunApp smt__CONSTANT__factorial__ smt__CONSTANT__n__)
        (ite (= smt__CONSTANT__n__ (smt__TLA____Cast__Int 0))
          (smt__TLA____Cast__Int 1)
          (smt__TLA____IntTimes smt__CONSTANT__n__
            (smt__TLA____FunApp smt__CONSTANT__factorial__
              (smt__TLA____IntMinus smt__CONSTANT__n__
                (smt__TLA____Cast__Int 1)))))))))

; omitted fact (second-order)

;; Goal
(assert
  (!
    (not
      (forall ((smt__CONSTANT__n__ Idv))
        (=> (smt__TLA____Mem smt__CONSTANT__n__ smt__TLA____NatSet)
          (=>
            (and
              (not
                (= (smt__CONSTANT__IsPrime__ smt__CONSTANT__n__)
                  smt__TLA____Tt__Idv))
              (distinct smt__CONSTANT__n__ (smt__TLA____Cast__Int 4)))
            (=
              (smt__TLA____IntRemainder
                (smt__TLA____FunApp smt__CONSTANT__factorial__
                  (smt__TLA____IntMinus smt__CONSTANT__n__
                    (smt__TLA____Cast__Int 1))) smt__CONSTANT__n__)
              (smt__TLA____Cast__Int 0)))))) :named |Goal|))

(check-sat)
(exit)
