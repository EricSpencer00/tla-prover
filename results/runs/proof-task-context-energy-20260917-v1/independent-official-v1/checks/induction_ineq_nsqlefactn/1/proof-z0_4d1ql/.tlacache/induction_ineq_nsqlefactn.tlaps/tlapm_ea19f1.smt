;; Proof obligation:
;;	ASSUME CONSTANT_NatInductiveDefHypothesis_(CONSTANT_factorial_, 1,
;;	                                           LAMBDA Unknown_v_, Unknown_n_ :
;;	                                             Unknown_n_ * Unknown_v_) ,
;;	       ASSUME NEW CONSTANT CONSTANT_Def_(_, _),
;;	              NEW CONSTANT CONSTANT_f_,
;;	              NEW CONSTANT CONSTANT_f0_,
;;	              CONSTANT_NatInductiveDefHypothesis_(CONSTANT_f_, CONSTANT_f0_,
;;	                                                  CONSTANT_Def_) 
;;	       PROVE  CONSTANT_NatInductiveDefConclusion_(CONSTANT_f_, CONSTANT_f0_,
;;	                                                  CONSTANT_Def_) 
;;	PROVE  CONSTANT_NatInductiveDefConclusion_(CONSTANT_factorial_, 1,
;;	                                           LAMBDA Unknown_v_, Unknown_n_ :
;;	                                             Unknown_n_ * Unknown_v_)
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./induction_ineq_nsqlefactn.tla", line 10, characters 3-4

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Cast__Int (Int) Idv)

(declare-fun smt__TLA____IntSet () Idv)

(declare-fun smt__TLA____IntTimes (Idv Idv) Idv)

(declare-fun smt__TLA____Mem (Idv Idv) Bool)

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

(declare-fun smt__CONSTANT__NatInductiveDefHypothesis____flatnd__1 (Idv
  Idv) Idv)

(assert
  (=
    (smt__CONSTANT__NatInductiveDefHypothesis____flatnd__1
      smt__CONSTANT__factorial__ (smt__TLA____Cast__Int 1))
    smt__TLA____Tt__Idv))

; omitted fact (second-order)

(declare-fun smt__CONSTANT__NatInductiveDefConclusion____flatnd__2 (Idv
  Idv) Idv)

;; Goal
(assert
  (!
    (not
      (=
        (smt__CONSTANT__NatInductiveDefConclusion____flatnd__2
          smt__CONSTANT__factorial__ (smt__TLA____Cast__Int 1))
        smt__TLA____Tt__Idv)) :named |Goal|))

(check-sat)
(exit)
