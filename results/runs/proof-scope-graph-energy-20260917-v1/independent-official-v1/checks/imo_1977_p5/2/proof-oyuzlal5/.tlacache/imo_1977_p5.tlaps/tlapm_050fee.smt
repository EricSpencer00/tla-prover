;; Proof obligation:
;;	\A CONSTANT_a_, CONSTANT_b_, CONSTANT_q_, CONSTANT_r_ \in Int :
;;	   CONSTANT_a_ >= 0 /\ CONSTANT_b_ >= 0 /\ CONSTANT_r_ >= 0
;;	   /\ CONSTANT_q_ >= 0
;;	   /\ (CONSTANT_r_ < CONSTANT_a_ + CONSTANT_b_
;;	       /\ CONSTANT_a_ * CONSTANT_a_ + CONSTANT_b_ * CONSTANT_b_
;;	          = (CONSTANT_a_ + CONSTANT_b_) * CONSTANT_q_ + CONSTANT_r_
;;	       /\ CONSTANT_q_ * CONSTANT_q_ + CONSTANT_r_ = 1977)
;;	   => (CONSTANT_ABS_(CONSTANT_a_ - 22) = 15
;;	       /\ CONSTANT_ABS_(CONSTANT_b_ - 22) = 28)
;;	      \/ (CONSTANT_ABS_(CONSTANT_a_ - 22) = 28
;;	          /\ CONSTANT_ABS_(CONSTANT_b_ - 22) = 15)
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./imo_1977_p5.tla", line 10, characters 89-90

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

(declare-fun smt__CONSTANT__ABS__ (Idv) Idv)

;; Goal
(assert
  (!
    (not
      (forall
        ((smt__CONSTANT__a__ Idv) (smt__CONSTANT__b__ Idv)
          (smt__CONSTANT__q__ Idv) (smt__CONSTANT__r__ Idv))
        (=>
          (and (smt__TLA____Mem smt__CONSTANT__a__ smt__TLA____IntSet)
            (smt__TLA____Mem smt__CONSTANT__b__ smt__TLA____IntSet)
            (smt__TLA____Mem smt__CONSTANT__q__ smt__TLA____IntSet)
            (smt__TLA____Mem smt__CONSTANT__r__ smt__TLA____IntSet))
          (=>
            (and
              (and
                (and
                  (and
                    (smt__TLA____IntLteq (smt__TLA____Cast__Int 0)
                      smt__CONSTANT__a__)
                    (smt__TLA____IntLteq (smt__TLA____Cast__Int 0)
                      smt__CONSTANT__b__))
                  (smt__TLA____IntLteq (smt__TLA____Cast__Int 0)
                    smt__CONSTANT__r__))
                (smt__TLA____IntLteq (smt__TLA____Cast__Int 0)
                  smt__CONSTANT__q__))
              (and
                (and
                  (and
                    (smt__TLA____IntLteq smt__CONSTANT__r__
                      (smt__TLA____IntPlus smt__CONSTANT__a__
                        smt__CONSTANT__b__))
                    (distinct smt__CONSTANT__r__
                      (smt__TLA____IntPlus smt__CONSTANT__a__
                        smt__CONSTANT__b__)))
                  (=
                    (smt__TLA____IntPlus
                      (smt__TLA____IntTimes smt__CONSTANT__a__
                        smt__CONSTANT__a__)
                      (smt__TLA____IntTimes smt__CONSTANT__b__
                        smt__CONSTANT__b__))
                    (smt__TLA____IntPlus
                      (smt__TLA____IntTimes
                        (smt__TLA____IntPlus smt__CONSTANT__a__
                          smt__CONSTANT__b__) smt__CONSTANT__q__)
                      smt__CONSTANT__r__)))
                (=
                  (smt__TLA____IntPlus
                    (smt__TLA____IntTimes smt__CONSTANT__q__
                      smt__CONSTANT__q__) smt__CONSTANT__r__)
                  (smt__TLA____Cast__Int 1977))))
            (or
              (and
                (=
                  (smt__CONSTANT__ABS__
                    (smt__TLA____IntMinus smt__CONSTANT__a__
                      (smt__TLA____Cast__Int 22))) (smt__TLA____Cast__Int 15))
                (=
                  (smt__CONSTANT__ABS__
                    (smt__TLA____IntMinus smt__CONSTANT__b__
                      (smt__TLA____Cast__Int 22))) (smt__TLA____Cast__Int 28)))
              (and
                (=
                  (smt__CONSTANT__ABS__
                    (smt__TLA____IntMinus smt__CONSTANT__a__
                      (smt__TLA____Cast__Int 22))) (smt__TLA____Cast__Int 28))
                (=
                  (smt__CONSTANT__ABS__
                    (smt__TLA____IntMinus smt__CONSTANT__b__
                      (smt__TLA____Cast__Int 22))) (smt__TLA____Cast__Int 15))))))))
    :named |Goal|))

(check-sat)
(exit)
