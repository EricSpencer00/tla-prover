;; Proof obligation:
;;	ASSUME \A CONSTANT_S_ : \E CONSTANT_x_ : CONSTANT_x_ \notin CONSTANT_S_ ,
;;	       \A CONSTANT_S_, CONSTANT_T_ :
;;	          (\A CONSTANT_x_ :
;;	              CONSTANT_x_ \in CONSTANT_S_ <=> CONSTANT_x_ \in CONSTANT_T_)
;;	          => CONSTANT_S_ = CONSTANT_T_ 
;;	PROVE  \A CONSTANT_a_ \in Int :
;;	          CONSTANT_a_ * CONSTANT_a_ % 4 = 0
;;	          \/ CONSTANT_a_ * CONSTANT_a_ % 4 = 1
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./numbertheory_sqmod4in01d.tla", line 5, characters 56-57

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Cast__Int (Int) Idv)

(declare-fun smt__TLA____IntRemainder (Idv Idv) Idv)

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

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_EnabledWrapper_' (second-order)

; omitted declaration of 'CONSTANT_CdotWrapper_' (second-order)

(assert
  (forall ((smt__CONSTANT__S__ Idv))
    (exists ((smt__CONSTANT__x__ Idv))
      (not (smt__TLA____Mem smt__CONSTANT__x__ smt__CONSTANT__S__)))))

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
      (forall ((smt__CONSTANT__a__ Idv))
        (=> (smt__TLA____Mem smt__CONSTANT__a__ smt__TLA____IntSet)
          (or
            (=
              (smt__TLA____IntRemainder
                (smt__TLA____IntTimes smt__CONSTANT__a__ smt__CONSTANT__a__)
                (smt__TLA____Cast__Int 4)) (smt__TLA____Cast__Int 0))
            (=
              (smt__TLA____IntRemainder
                (smt__TLA____IntTimes smt__CONSTANT__a__ smt__CONSTANT__a__)
                (smt__TLA____Cast__Int 4)) (smt__TLA____Cast__Int 1))))))
    :named |Goal|))

(check-sat)
(exit)
