;; Proof obligation:
;;	\A CONSTANT_a_, CONSTANT_b_ \in Nat :
;;	   CONSTANT_a_ > 1
;;	   /\ (\A CONSTANT_m_ \in 2..CONSTANT_a_ - 1 :
;;	          ~(\E CONSTANT_p_ \in 2..CONSTANT_a_ - 1 :
;;	               CONSTANT_a_ = CONSTANT_m_ * CONSTANT_p_))
;;	   /\ (CONSTANT_b_ > 1
;;	       /\ (\A CONSTANT_m_ \in 2..CONSTANT_b_ - 1 :
;;	              ~(\E CONSTANT_p_ \in 2..CONSTANT_b_ - 1 :
;;	                   CONSTANT_b_ = CONSTANT_m_ * CONSTANT_p_)))
;;	   /\ (CONSTANT_a_ - CONSTANT_b_ > 1
;;	       /\ (\A CONSTANT_m_ \in 2..CONSTANT_a_ - CONSTANT_b_ - 1 :
;;	              ~(\E CONSTANT_p_ \in 2..CONSTANT_a_ - CONSTANT_b_ - 1 :
;;	                   CONSTANT_a_ - CONSTANT_b_ = CONSTANT_m_ * CONSTANT_p_)))
;;	   /\ (CONSTANT_a_ + CONSTANT_b_ > 1
;;	       /\ (\A CONSTANT_m_ \in 2..(CONSTANT_a_ + CONSTANT_b_) - 1 :
;;	              ~(\E CONSTANT_p_ \in 2..(CONSTANT_a_ + CONSTANT_b_) - 1 :
;;	                   CONSTANT_a_ + CONSTANT_b_ = CONSTANT_m_ * CONSTANT_p_)))
;;	   => CONSTANT_a_ + CONSTANT_b_
;;	      + (CONSTANT_a_ - CONSTANT_b_ + (CONSTANT_a_ + CONSTANT_b_)) > 1
;;	      /\ (\A CONSTANT_m_
;;	             \in 2..(CONSTANT_a_ + CONSTANT_b_
;;	                     + (CONSTANT_a_ - CONSTANT_b_
;;	                        + (CONSTANT_a_ + CONSTANT_b_)))
;;	                    - 1 :
;;	             ~(\E CONSTANT_p_
;;	                  \in 2..(CONSTANT_a_ + CONSTANT_b_
;;	                          + (CONSTANT_a_ - CONSTANT_b_
;;	                             + (CONSTANT_a_ + CONSTANT_b_)))
;;	                         - 1 :
;;	                  CONSTANT_a_ + CONSTANT_b_
;;	                  + (CONSTANT_a_ - CONSTANT_b_ + (CONSTANT_a_ + CONSTANT_b_))
;;	                  = CONSTANT_m_ * CONSTANT_p_))
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./amc12b_2002_p11.tla", line 8, characters 107-108

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Cast__Int (Int) Idv)

(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)

(declare-fun smt__TLA____IntMinus (Idv Idv) Idv)

(declare-fun smt__TLA____IntPlus (Idv Idv) Idv)

(declare-fun smt__TLA____IntRange (Idv Idv) Idv)

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
                  (and
                    (and
                      (smt__TLA____IntLteq (smt__TLA____Cast__Int 1)
                        smt__CONSTANT__a__)
                      (distinct (smt__TLA____Cast__Int 1) smt__CONSTANT__a__))
                    (forall ((smt__CONSTANT__m__ Idv))
                      (=>
                        (smt__TLA____Mem smt__CONSTANT__m__
                          (smt__TLA____IntRange (smt__TLA____Cast__Int 2)
                            (smt__TLA____IntMinus smt__CONSTANT__a__
                              (smt__TLA____Cast__Int 1))))
                        (not
                          (exists ((smt__CONSTANT__p__ Idv))
                            (and
                              (smt__TLA____Mem smt__CONSTANT__p__
                                (smt__TLA____IntRange
                                  (smt__TLA____Cast__Int 2)
                                  (smt__TLA____IntMinus smt__CONSTANT__a__
                                    (smt__TLA____Cast__Int 1))))
                              (= smt__CONSTANT__a__
                                (smt__TLA____IntTimes smt__CONSTANT__m__
                                  smt__CONSTANT__p__))))))))
                  (and
                    (and
                      (smt__TLA____IntLteq (smt__TLA____Cast__Int 1)
                        smt__CONSTANT__b__)
                      (distinct (smt__TLA____Cast__Int 1) smt__CONSTANT__b__))
                    (forall ((smt__CONSTANT__m__ Idv))
                      (=>
                        (smt__TLA____Mem smt__CONSTANT__m__
                          (smt__TLA____IntRange (smt__TLA____Cast__Int 2)
                            (smt__TLA____IntMinus smt__CONSTANT__b__
                              (smt__TLA____Cast__Int 1))))
                        (not
                          (exists ((smt__CONSTANT__p__ Idv))
                            (and
                              (smt__TLA____Mem smt__CONSTANT__p__
                                (smt__TLA____IntRange
                                  (smt__TLA____Cast__Int 2)
                                  (smt__TLA____IntMinus smt__CONSTANT__b__
                                    (smt__TLA____Cast__Int 1))))
                              (= smt__CONSTANT__b__
                                (smt__TLA____IntTimes smt__CONSTANT__m__
                                  smt__CONSTANT__p__)))))))))
                (and
                  (and
                    (smt__TLA____IntLteq (smt__TLA____Cast__Int 1)
                      (smt__TLA____IntMinus smt__CONSTANT__a__
                        smt__CONSTANT__b__))
                    (distinct (smt__TLA____Cast__Int 1)
                      (smt__TLA____IntMinus smt__CONSTANT__a__
                        smt__CONSTANT__b__)))
                  (forall ((smt__CONSTANT__m__ Idv))
                    (=>
                      (smt__TLA____Mem smt__CONSTANT__m__
                        (smt__TLA____IntRange (smt__TLA____Cast__Int 2)
                          (smt__TLA____IntMinus
                            (smt__TLA____IntMinus smt__CONSTANT__a__
                              smt__CONSTANT__b__) (smt__TLA____Cast__Int 1))))
                      (not
                        (exists ((smt__CONSTANT__p__ Idv))
                          (and
                            (smt__TLA____Mem smt__CONSTANT__p__
                              (smt__TLA____IntRange (smt__TLA____Cast__Int 2)
                                (smt__TLA____IntMinus
                                  (smt__TLA____IntMinus smt__CONSTANT__a__
                                    smt__CONSTANT__b__)
                                  (smt__TLA____Cast__Int 1))))
                            (=
                              (smt__TLA____IntMinus smt__CONSTANT__a__
                                smt__CONSTANT__b__)
                              (smt__TLA____IntTimes smt__CONSTANT__m__
                                smt__CONSTANT__p__)))))))))
              (and
                (and
                  (smt__TLA____IntLteq (smt__TLA____Cast__Int 1)
                    (smt__TLA____IntPlus smt__CONSTANT__a__
                      smt__CONSTANT__b__))
                  (distinct (smt__TLA____Cast__Int 1)
                    (smt__TLA____IntPlus smt__CONSTANT__a__
                      smt__CONSTANT__b__)))
                (forall ((smt__CONSTANT__m__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__m__
                      (smt__TLA____IntRange (smt__TLA____Cast__Int 2)
                        (smt__TLA____IntMinus
                          (smt__TLA____IntPlus smt__CONSTANT__a__
                            smt__CONSTANT__b__) (smt__TLA____Cast__Int 1))))
                    (not
                      (exists ((smt__CONSTANT__p__ Idv))
                        (and
                          (smt__TLA____Mem smt__CONSTANT__p__
                            (smt__TLA____IntRange (smt__TLA____Cast__Int 2)
                              (smt__TLA____IntMinus
                                (smt__TLA____IntPlus smt__CONSTANT__a__
                                  smt__CONSTANT__b__)
                                (smt__TLA____Cast__Int 1))))
                          (=
                            (smt__TLA____IntPlus smt__CONSTANT__a__
                              smt__CONSTANT__b__)
                            (smt__TLA____IntTimes smt__CONSTANT__m__
                              smt__CONSTANT__p__)))))))))
            (and
              (and
                (smt__TLA____IntLteq (smt__TLA____Cast__Int 1)
                  (smt__TLA____IntPlus
                    (smt__TLA____IntPlus smt__CONSTANT__a__
                      smt__CONSTANT__b__)
                    (smt__TLA____IntPlus
                      (smt__TLA____IntMinus smt__CONSTANT__a__
                        smt__CONSTANT__b__)
                      (smt__TLA____IntPlus smt__CONSTANT__a__
                        smt__CONSTANT__b__))))
                (distinct (smt__TLA____Cast__Int 1)
                  (smt__TLA____IntPlus
                    (smt__TLA____IntPlus smt__CONSTANT__a__
                      smt__CONSTANT__b__)
                    (smt__TLA____IntPlus
                      (smt__TLA____IntMinus smt__CONSTANT__a__
                        smt__CONSTANT__b__)
                      (smt__TLA____IntPlus smt__CONSTANT__a__
                        smt__CONSTANT__b__)))))
              (forall ((smt__CONSTANT__m__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__m__
                    (smt__TLA____IntRange (smt__TLA____Cast__Int 2)
                      (smt__TLA____IntMinus
                        (smt__TLA____IntPlus
                          (smt__TLA____IntPlus smt__CONSTANT__a__
                            smt__CONSTANT__b__)
                          (smt__TLA____IntPlus
                            (smt__TLA____IntMinus smt__CONSTANT__a__
                              smt__CONSTANT__b__)
                            (smt__TLA____IntPlus smt__CONSTANT__a__
                              smt__CONSTANT__b__))) (smt__TLA____Cast__Int 1))))
                  (not
                    (exists ((smt__CONSTANT__p__ Idv))
                      (and
                        (smt__TLA____Mem smt__CONSTANT__p__
                          (smt__TLA____IntRange (smt__TLA____Cast__Int 2)
                            (smt__TLA____IntMinus
                              (smt__TLA____IntPlus
                                (smt__TLA____IntPlus smt__CONSTANT__a__
                                  smt__CONSTANT__b__)
                                (smt__TLA____IntPlus
                                  (smt__TLA____IntMinus smt__CONSTANT__a__
                                    smt__CONSTANT__b__)
                                  (smt__TLA____IntPlus smt__CONSTANT__a__
                                    smt__CONSTANT__b__)))
                              (smt__TLA____Cast__Int 1))))
                        (=
                          (smt__TLA____IntPlus
                            (smt__TLA____IntPlus smt__CONSTANT__a__
                              smt__CONSTANT__b__)
                            (smt__TLA____IntPlus
                              (smt__TLA____IntMinus smt__CONSTANT__a__
                                smt__CONSTANT__b__)
                              (smt__TLA____IntPlus smt__CONSTANT__a__
                                smt__CONSTANT__b__)))
                          (smt__TLA____IntTimes smt__CONSTANT__m__
                            smt__CONSTANT__p__)))))))))))) :named |Goal|))

(check-sat)
(exit)
