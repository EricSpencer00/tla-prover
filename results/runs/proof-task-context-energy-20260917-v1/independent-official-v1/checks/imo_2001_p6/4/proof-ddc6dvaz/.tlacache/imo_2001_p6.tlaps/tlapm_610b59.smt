;; Proof obligation:
;;	ASSUME \A CONSTANT_S_, CONSTANT_T_ :
;;	          (\A CONSTANT_x_ :
;;	              CONSTANT_x_ \in CONSTANT_S_ <=> CONSTANT_x_ \in CONSTANT_T_)
;;	          => CONSTANT_S_ = CONSTANT_T_ 
;;	PROVE  \A CONSTANT_a_, CONSTANT_b_, CONSTANT_c_, CONSTANT_d_ \in Nat :
;;	          CONSTANT_a_ > 0 /\ CONSTANT_b_ > 0 /\ CONSTANT_c_ > 0
;;	          /\ CONSTANT_d_ > 0 /\ CONSTANT_a_ > CONSTANT_b_
;;	          /\ CONSTANT_b_ > CONSTANT_c_ /\ CONSTANT_c_ > CONSTANT_d_
;;	          /\ CONSTANT_a_ * CONSTANT_c_ + CONSTANT_b_ * CONSTANT_d_
;;	             = (CONSTANT_b_ + CONSTANT_d_ + CONSTANT_a_ - CONSTANT_c_)
;;	               * (CONSTANT_b_ + CONSTANT_d_ + CONSTANT_c_ - CONSTANT_a_)
;;	          => ~CONSTANT_IsPrime_(CONSTANT_a_ * CONSTANT_b_
;;	                                + CONSTANT_c_ * CONSTANT_d_)
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./imo_2001_p6.tla", line 13, characters 28-29

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Cast__Int (Int) Idv)

(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)

(declare-fun smt__TLA____IntMinus (Idv Idv) Idv)

(declare-fun smt__TLA____IntPlus (Idv Idv) Idv)

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

(declare-fun smt__CONSTANT__IsPrime__ (Idv) Idv)

(assert
  (forall ((smt__CONSTANT__S__ Idv) (smt__CONSTANT__T__ Idv))
    (=>
      (forall ((smt__CONSTANT__x__ Idv))
        (= (smt__TLA____Mem smt__CONSTANT__x__ smt__CONSTANT__S__)
          (smt__TLA____Mem smt__CONSTANT__x__ smt__CONSTANT__T__)))
      (= smt__CONSTANT__S__ smt__CONSTANT__T__))))

;; Goal
(assert
  (!
    (not
      (forall
        ((smt__CONSTANT__a__ Idv) (smt__CONSTANT__b__ Idv)
          (smt__CONSTANT__c__ Idv) (smt__CONSTANT__d__ Idv))
        (=>
          (and (smt__TLA____Mem smt__CONSTANT__a__ smt__TLA____NatSet)
            (smt__TLA____Mem smt__CONSTANT__b__ smt__TLA____NatSet)
            (smt__TLA____Mem smt__CONSTANT__c__ smt__TLA____NatSet)
            (smt__TLA____Mem smt__CONSTANT__d__ smt__TLA____NatSet))
          (=>
            (and
              (and
                (and
                  (and
                    (and
                      (and
                        (and
                          (and
                            (smt__TLA____IntLteq (smt__TLA____Cast__Int 0)
                              smt__CONSTANT__a__)
                            (distinct (smt__TLA____Cast__Int 0)
                              smt__CONSTANT__a__))
                          (and
                            (smt__TLA____IntLteq (smt__TLA____Cast__Int 0)
                              smt__CONSTANT__b__)
                            (distinct (smt__TLA____Cast__Int 0)
                              smt__CONSTANT__b__)))
                        (and
                          (smt__TLA____IntLteq (smt__TLA____Cast__Int 0)
                            smt__CONSTANT__c__)
                          (distinct (smt__TLA____Cast__Int 0)
                            smt__CONSTANT__c__)))
                      (and
                        (smt__TLA____IntLteq (smt__TLA____Cast__Int 0)
                          smt__CONSTANT__d__)
                        (distinct (smt__TLA____Cast__Int 0)
                          smt__CONSTANT__d__)))
                    (and
                      (smt__TLA____IntLteq smt__CONSTANT__b__
                        smt__CONSTANT__a__)
                      (distinct smt__CONSTANT__b__ smt__CONSTANT__a__)))
                  (and
                    (smt__TLA____IntLteq smt__CONSTANT__c__
                      smt__CONSTANT__b__)
                    (distinct smt__CONSTANT__c__ smt__CONSTANT__b__)))
                (and
                  (smt__TLA____IntLteq smt__CONSTANT__d__ smt__CONSTANT__c__)
                  (distinct smt__CONSTANT__d__ smt__CONSTANT__c__)))
              (=
                (smt__TLA____IntPlus
                  (smt__TLA____IntTimes smt__CONSTANT__a__ smt__CONSTANT__c__)
                  (smt__TLA____IntTimes smt__CONSTANT__b__ smt__CONSTANT__d__))
                (smt__TLA____IntTimes
                  (smt__TLA____IntPlus
                    (smt__TLA____IntPlus smt__CONSTANT__b__
                      smt__CONSTANT__d__)
                    (smt__TLA____IntMinus smt__CONSTANT__a__
                      smt__CONSTANT__c__))
                  (smt__TLA____IntPlus
                    (smt__TLA____IntPlus smt__CONSTANT__b__
                      smt__CONSTANT__d__)
                    (smt__TLA____IntMinus smt__CONSTANT__c__
                      smt__CONSTANT__a__)))))
            (not
              (=
                (smt__CONSTANT__IsPrime__
                  (smt__TLA____IntPlus
                    (smt__TLA____IntTimes smt__CONSTANT__a__
                      smt__CONSTANT__b__)
                    (smt__TLA____IntTimes smt__CONSTANT__c__
                      smt__CONSTANT__d__))) smt__TLA____Tt__Idv))))))
    :named |Goal|))

(check-sat)
(exit)
