;; Proof obligation:
;;	ASSUME \A CONSTANT_S_, CONSTANT_T_ :
;;	          (\A CONSTANT_x_ :
;;	              CONSTANT_x_ \in CONSTANT_S_ <=> CONSTANT_x_ \in CONSTANT_T_)
;;	          => CONSTANT_S_ = CONSTANT_T_ ,
;;	       \A CONSTANT_S_ : \E CONSTANT_x_ : CONSTANT_x_ \notin CONSTANT_S_ 
;;	PROVE  \A CONSTANT_a_, CONSTANT_m_, CONSTANT_c_ \in Nat :
;;	          CONSTANT_a_ + CONSTANT_m_ + CONSTANT_c_ = 12
;;	          => CONSTANT_a_ * CONSTANT_m_ * CONSTANT_c_
;;	             + CONSTANT_a_ * CONSTANT_m_ + CONSTANT_m_ * CONSTANT_c_
;;	             + CONSTANT_a_ * CONSTANT_c_ =< 112
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./amc12_2000_p12.tla", line 7, characters 51-52

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Cast__Int (Int) Idv)

(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)

(declare-fun smt__TLA____IntPlus (Idv Idv) Idv)

(declare-fun smt__TLA____IntSet () Idv)

(declare-fun smt__TLA____IntTimes (Idv Idv) Idv)

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
      (forall
        ((smt__CONSTANT__a__ Idv) (smt__CONSTANT__m__ Idv)
          (smt__CONSTANT__c__ Idv))
        (=>
          (and (smt__TLA____Mem smt__CONSTANT__a__ smt__TLA____NatSet)
            (smt__TLA____Mem smt__CONSTANT__m__ smt__TLA____NatSet)
            (smt__TLA____Mem smt__CONSTANT__c__ smt__TLA____NatSet))
          (=>
            (=
              (smt__TLA____IntPlus
                (smt__TLA____IntPlus smt__CONSTANT__a__ smt__CONSTANT__m__)
                smt__CONSTANT__c__) (smt__TLA____Cast__Int 12))
            (smt__TLA____IntLteq
              (smt__TLA____IntPlus
                (smt__TLA____IntPlus
                  (smt__TLA____IntPlus
                    (smt__TLA____IntTimes
                      (smt__TLA____IntTimes smt__CONSTANT__a__
                        smt__CONSTANT__m__) smt__CONSTANT__c__)
                    (smt__TLA____IntTimes smt__CONSTANT__a__
                      smt__CONSTANT__m__))
                  (smt__TLA____IntTimes smt__CONSTANT__m__ smt__CONSTANT__c__))
                (smt__TLA____IntTimes smt__CONSTANT__a__ smt__CONSTANT__c__))
              (smt__TLA____Cast__Int 112)))))) :named |Goal|))

(check-sat)
(exit)
