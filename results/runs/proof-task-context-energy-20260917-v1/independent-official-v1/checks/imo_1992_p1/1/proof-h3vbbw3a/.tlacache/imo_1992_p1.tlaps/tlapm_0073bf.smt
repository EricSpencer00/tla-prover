;; Proof obligation:
;;	\A CONSTANT_p_, CONSTANT_q_, CONSTANT_r_ \in Int :
;;	   1 < CONSTANT_p_ /\ CONSTANT_p_ < CONSTANT_q_ /\ CONSTANT_q_ < CONSTANT_r_
;;	   /\ (\E CONSTANT_k_ \in Int :
;;	          CONSTANT_p_ * CONSTANT_q_ * CONSTANT_r_ - 1
;;	          = CONSTANT_k_
;;	            * ((CONSTANT_p_ - 1) * (CONSTANT_q_ - 1) * (CONSTANT_r_ - 1)))
;;	   => (CONSTANT_p_ = 2 /\ CONSTANT_q_ = 4 /\ CONSTANT_r_ = 8)
;;	      \/ (CONSTANT_p_ = 3 /\ CONSTANT_q_ = 5 /\ CONSTANT_r_ = 15)
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./imo_1992_p1.tla", line 10, characters 64-65

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Cast__Int (Int) Idv)

(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)

(declare-fun smt__TLA____IntMinus (Idv Idv) Idv)

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

;; Goal
(assert
  (!
    (not
      (forall
        ((smt__CONSTANT__p__ Idv) (smt__CONSTANT__q__ Idv)
          (smt__CONSTANT__r__ Idv))
        (=>
          (and (smt__TLA____Mem smt__CONSTANT__p__ smt__TLA____IntSet)
            (smt__TLA____Mem smt__CONSTANT__q__ smt__TLA____IntSet)
            (smt__TLA____Mem smt__CONSTANT__r__ smt__TLA____IntSet))
          (=>
            (and
              (and
                (and
                  (and
                    (smt__TLA____IntLteq (smt__TLA____Cast__Int 1)
                      smt__CONSTANT__p__)
                    (distinct (smt__TLA____Cast__Int 1) smt__CONSTANT__p__))
                  (and
                    (smt__TLA____IntLteq smt__CONSTANT__p__
                      smt__CONSTANT__q__)
                    (distinct smt__CONSTANT__p__ smt__CONSTANT__q__)))
                (and
                  (smt__TLA____IntLteq smt__CONSTANT__q__ smt__CONSTANT__r__)
                  (distinct smt__CONSTANT__q__ smt__CONSTANT__r__)))
              (exists ((smt__CONSTANT__k__ Idv))
                (and (smt__TLA____Mem smt__CONSTANT__k__ smt__TLA____IntSet)
                  (=
                    (smt__TLA____IntMinus
                      (smt__TLA____IntTimes
                        (smt__TLA____IntTimes smt__CONSTANT__p__
                          smt__CONSTANT__q__) smt__CONSTANT__r__)
                      (smt__TLA____Cast__Int 1))
                    (smt__TLA____IntTimes smt__CONSTANT__k__
                      (smt__TLA____IntTimes
                        (smt__TLA____IntTimes
                          (smt__TLA____IntMinus smt__CONSTANT__p__
                            (smt__TLA____Cast__Int 1))
                          (smt__TLA____IntMinus smt__CONSTANT__q__
                            (smt__TLA____Cast__Int 1)))
                        (smt__TLA____IntMinus smt__CONSTANT__r__
                          (smt__TLA____Cast__Int 1))))))))
            (or
              (and
                (and (= smt__CONSTANT__p__ (smt__TLA____Cast__Int 2))
                  (= smt__CONSTANT__q__ (smt__TLA____Cast__Int 4)))
                (= smt__CONSTANT__r__ (smt__TLA____Cast__Int 8)))
              (and
                (and (= smt__CONSTANT__p__ (smt__TLA____Cast__Int 3))
                  (= smt__CONSTANT__q__ (smt__TLA____Cast__Int 5)))
                (= smt__CONSTANT__r__ (smt__TLA____Cast__Int 15))))))))
    :named |Goal|))

(check-sat)
(exit)
