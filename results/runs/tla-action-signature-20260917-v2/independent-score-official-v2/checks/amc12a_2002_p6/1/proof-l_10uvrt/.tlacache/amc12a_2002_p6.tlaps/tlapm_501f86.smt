;; Proof obligation:
;;	\A CONSTANT_n_ \in Nat \ {0} :
;;	   \E CONSTANT_m_ \in Nat :
;;	      CONSTANT_m_ > CONSTANT_n_
;;	      /\ (\E CONSTANT_p_ \in Nat :
;;	             CONSTANT_m_ * CONSTANT_p_ =< CONSTANT_m_ + CONSTANT_p_)
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./amc12a_2002_p6.tla", line 6, characters 51-52

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

(declare-fun smt__TLA____SetEnum__1 (Idv) Idv)

(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLA____SetMinus (Idv Idv) Idv)

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

;; Axiom: SetMinusDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (= (smt__TLA____Mem smt__x (smt__TLA____SetMinus smt__a smt__b))
          (and (smt__TLA____Mem smt__x smt__a)
            (not (smt__TLA____Mem smt__x smt__b))))
        :pattern ((smt__TLA____Mem smt__x
                    (smt__TLA____SetMinus smt__a smt__b)))
        :pattern ((smt__TLA____Mem smt__x smt__a)
                   (smt__TLA____SetMinus smt__a smt__b))
        :pattern ((smt__TLA____Mem smt__x smt__b)
                   (smt__TLA____SetMinus smt__a smt__b))))
    :named |SetMinusDef|))

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

;; Axiom: EnumDefIntro 1
(assert
  (!
    (forall ((smt__a1 Idv))
      (! (smt__TLA____Mem smt__a1 (smt__TLA____SetEnum__1 smt__a1))
        :pattern ((smt__TLA____SetEnum__1 smt__a1)))) :named |EnumDefIntro 1|))

;; Axiom: EnumDefElim 1
(assert
  (!
    (forall ((smt__a1 Idv) (smt__x Idv))
      (!
        (=> (smt__TLA____Mem smt__x (smt__TLA____SetEnum__1 smt__a1))
          (= smt__x smt__a1))
        :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetEnum__1 smt__a1)))))
    :named |EnumDefElim 1|))

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
      (forall ((smt__CONSTANT__n__ Idv))
        (=>
          (smt__TLA____Mem smt__CONSTANT__n__
            (smt__TLA____SetMinus smt__TLA____NatSet
              (smt__TLA____SetEnum__1 (smt__TLA____Cast__Int 0))))
          (exists ((smt__CONSTANT__m__ Idv))
            (and (smt__TLA____Mem smt__CONSTANT__m__ smt__TLA____NatSet)
              (and
                (and
                  (smt__TLA____IntLteq smt__CONSTANT__n__ smt__CONSTANT__m__)
                  (distinct smt__CONSTANT__n__ smt__CONSTANT__m__))
                (exists ((smt__CONSTANT__p__ Idv))
                  (and
                    (smt__TLA____Mem smt__CONSTANT__p__ smt__TLA____NatSet)
                    (smt__TLA____IntLteq
                      (smt__TLA____IntTimes smt__CONSTANT__m__
                        smt__CONSTANT__p__)
                      (smt__TLA____IntPlus smt__CONSTANT__m__
                        smt__CONSTANT__p__)))))))))) :named |Goal|))

(check-sat)
(exit)
