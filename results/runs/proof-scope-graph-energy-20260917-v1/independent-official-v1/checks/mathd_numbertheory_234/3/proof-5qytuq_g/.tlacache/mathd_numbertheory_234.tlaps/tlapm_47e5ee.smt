;; Proof obligation:
;;	\A CONSTANT_a_, CONSTANT_b_ \in Nat :
;;	   CONSTANT_a_ >= 1 /\ CONSTANT_a_ =< 9 /\ CONSTANT_b_ =< 9
;;	   /\ (10 * CONSTANT_a_ + CONSTANT_b_) * (10 * CONSTANT_a_ + CONSTANT_b_)
;;	      * (10 * CONSTANT_a_ + CONSTANT_b_) = 912673
;;	   => CONSTANT_a_ + CONSTANT_b_ = 16
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./mathd_numbertheory_234.tla", line 9, characters 1-2

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

;; Goal
(assert
  (!
    (not
      (forall ((smt__CONSTANT__a__ Idv) (smt__CONSTANT__b__ Idv))
        (=>
          (and (smt__TLA____Mem smt__CONSTANT__a__ smt__TLA____NatSet)
            (smt__TLA____Mem smt__CONSTANT__b__ smt__TLA____NatSet))
          (=>
            (and
              (and
                (and
                  (smt__TLA____IntLteq (smt__TLA____Cast__Int 1)
                    smt__CONSTANT__a__)
                  (smt__TLA____IntLteq smt__CONSTANT__a__
                    (smt__TLA____Cast__Int 9)))
                (smt__TLA____IntLteq smt__CONSTANT__b__
                  (smt__TLA____Cast__Int 9)))
              (=
                (smt__TLA____IntTimes
                  (smt__TLA____IntTimes
                    (smt__TLA____IntPlus
                      (smt__TLA____IntTimes (smt__TLA____Cast__Int 10)
                        smt__CONSTANT__a__) smt__CONSTANT__b__)
                    (smt__TLA____IntPlus
                      (smt__TLA____IntTimes (smt__TLA____Cast__Int 10)
                        smt__CONSTANT__a__) smt__CONSTANT__b__))
                  (smt__TLA____IntPlus
                    (smt__TLA____IntTimes (smt__TLA____Cast__Int 10)
                      smt__CONSTANT__a__) smt__CONSTANT__b__))
                (smt__TLA____Cast__Int 912673)))
            (= (smt__TLA____IntPlus smt__CONSTANT__a__ smt__CONSTANT__b__)
              (smt__TLA____Cast__Int 16)))))) :named |Goal|))

(check-sat)
(exit)
