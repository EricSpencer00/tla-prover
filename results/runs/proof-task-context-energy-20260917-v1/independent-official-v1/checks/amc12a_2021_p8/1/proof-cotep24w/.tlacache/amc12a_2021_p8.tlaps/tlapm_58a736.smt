;; Proof obligation:
;;	CONSTANT_D_[2021] % 2 = 0 /\ CONSTANT_D_[2022] % 2 = 1
;;	/\ CONSTANT_D_[2023] % 2 = 0
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./amc12a_2021_p8.tla", line 13, characters 51-52

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Cast__Int (Int) Idv)

(declare-fun smt__TLA____FunApp (Idv Idv) Idv)

(declare-fun smt__TLA____FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA____FunIsafcn (Idv) Bool)

(declare-fun smt__TLA____IntRemainder (Idv Idv) Idv)

(declare-fun smt__TLA____IntSet () Idv)

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

(declare-fun smt__CONSTANT__D__ () Idv)

;; Goal
(assert
  (!
    (not
      (and
        (and
          (=
            (smt__TLA____IntRemainder
              (smt__TLA____FunApp smt__CONSTANT__D__
                (smt__TLA____Cast__Int 2021)) (smt__TLA____Cast__Int 2))
            (smt__TLA____Cast__Int 0))
          (=
            (smt__TLA____IntRemainder
              (smt__TLA____FunApp smt__CONSTANT__D__
                (smt__TLA____Cast__Int 2022)) (smt__TLA____Cast__Int 2))
            (smt__TLA____Cast__Int 1)))
        (=
          (smt__TLA____IntRemainder
            (smt__TLA____FunApp smt__CONSTANT__D__
              (smt__TLA____Cast__Int 2023)) (smt__TLA____Cast__Int 2))
          (smt__TLA____Cast__Int 0)))) :named |Goal|))

(check-sat)
(exit)
