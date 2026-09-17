;; Proof obligation:
;;	(CHOOSE CONSTANT_factorial_ :
;;	   CONSTANT_factorial_
;;	   = [CONSTANT_n_ \in Nat |->
;;	        IF CONSTANT_n_ = 0
;;	          THEN 1
;;	          ELSE CONSTANT_n_ * CONSTANT_factorial_[CONSTANT_n_ - 1]])
;;	= (CHOOSE CONSTANT_g_ :
;;	     CONSTANT_g_
;;	     = [CONSTANT_i_ \in Nat |->
;;	          IF CONSTANT_i_ = 0
;;	            THEN 1
;;	            ELSE CONSTANT_i_ * CONSTANT_g_[CONSTANT_i_ - 1]])
;; TLA+ Proof Manager 80172c6
;; Proof obligation #4
;; Generated from file "./exercise_3_10.tla", line 8, characters 3-4

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Cast__Int (Int) Idv)

; omitted declaration of 'TLA__Choose' (second-order)

(declare-fun smt__TLA____FunApp (Idv Idv) Idv)

(declare-fun smt__TLA____FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA____FunIsafcn (Idv) Bool)

(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)

(declare-fun smt__TLA____IntMinus (Idv Idv) Idv)

(declare-fun smt__TLA____IntSet () Idv)

(declare-fun smt__TLA____IntTimes (Idv Idv) Idv)

(declare-fun smt__TLA____Mem (Idv Idv) Bool)

(declare-fun smt__TLA____NatSet () Idv)

(declare-fun smt__TLA____Proj__Int (Idv) Int)

(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)

; omitted fact (second-order)

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

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

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

; hidden fact

; hidden fact

(declare-fun smt__TLA____FunFcn__flatnd__1 (Idv Idv) Idv)

;; Axiom: FunConstrIsafcn TLA__FunFcn_flatnd_1
(assert
  (!
    (forall ((smt__CONSTANT__factorial__ Idv) (smt__a Idv))
      (!
        (smt__TLA____FunIsafcn
          (smt__TLA____FunFcn__flatnd__1 smt__a smt__CONSTANT__factorial__))
        :pattern ((smt__TLA____FunFcn__flatnd__1 smt__a
                    smt__CONSTANT__factorial__))))
    :named |FunConstrIsafcn TLA__FunFcn_flatnd_1|))

;; Axiom: FunDomDef TLA__FunFcn_flatnd_1
(assert
  (!
    (forall ((smt__CONSTANT__factorial__ Idv) (smt__a Idv))
      (!
        (=
          (smt__TLA____FunDom
            (smt__TLA____FunFcn__flatnd__1 smt__a smt__CONSTANT__factorial__))
          smt__a)
        :pattern ((smt__TLA____FunFcn__flatnd__1 smt__a
                    smt__CONSTANT__factorial__))))
    :named |FunDomDef TLA__FunFcn_flatnd_1|))

;; Axiom: FunAppDef TLA__FunFcn_flatnd_1
(assert
  (!
    (forall ((smt__CONSTANT__factorial__ Idv) (smt__a Idv) (smt__x Idv))
      (!
        (=> (smt__TLA____Mem smt__x smt__a)
          (=
            (smt__TLA____FunApp
              (smt__TLA____FunFcn__flatnd__1 smt__a
                smt__CONSTANT__factorial__) smt__x)
            (ite (= smt__x (smt__TLA____Cast__Int 0))
              (smt__TLA____Cast__Int 1)
              (smt__TLA____IntTimes smt__x
                (smt__TLA____FunApp smt__CONSTANT__factorial__
                  (smt__TLA____IntMinus smt__x (smt__TLA____Cast__Int 1)))))))
        :pattern ((smt__TLA____FunApp
                    (smt__TLA____FunFcn__flatnd__1 smt__a
                      smt__CONSTANT__factorial__) smt__x))
        :pattern ((smt__TLA____Mem smt__x smt__a)
                   (smt__TLA____FunFcn__flatnd__1 smt__a
                     smt__CONSTANT__factorial__))))
    :named |FunAppDef TLA__FunFcn_flatnd_1|))

(declare-fun smt__TLA____Choose__flatnd__2 () Idv)

;; Axiom: ChooseDef TLA__Choose_flatnd_2
(assert
  (!
    (forall ((smt__x Idv))
      (=>
        (= smt__x (smt__TLA____FunFcn__flatnd__1 smt__TLA____NatSet smt__x))
        (= smt__TLA____Choose__flatnd__2
          (smt__TLA____FunFcn__flatnd__1 smt__TLA____NatSet
            smt__TLA____Choose__flatnd__2))))
    :named |ChooseDef TLA__Choose_flatnd_2|))

(declare-fun smt__TLA____FunFcn__flatnd__3 (Idv Idv) Idv)

;; Axiom: FunConstrIsafcn TLA__FunFcn_flatnd_3
(assert
  (!
    (forall ((smt__CONSTANT__g__ Idv) (smt__a Idv))
      (!
        (smt__TLA____FunIsafcn
          (smt__TLA____FunFcn__flatnd__3 smt__a smt__CONSTANT__g__))
        :pattern ((smt__TLA____FunFcn__flatnd__3 smt__a smt__CONSTANT__g__))))
    :named |FunConstrIsafcn TLA__FunFcn_flatnd_3|))

;; Axiom: FunDomDef TLA__FunFcn_flatnd_3
(assert
  (!
    (forall ((smt__CONSTANT__g__ Idv) (smt__a Idv))
      (!
        (=
          (smt__TLA____FunDom
            (smt__TLA____FunFcn__flatnd__3 smt__a smt__CONSTANT__g__)) 
          smt__a)
        :pattern ((smt__TLA____FunFcn__flatnd__3 smt__a smt__CONSTANT__g__))))
    :named |FunDomDef TLA__FunFcn_flatnd_3|))

;; Axiom: FunAppDef TLA__FunFcn_flatnd_3
(assert
  (!
    (forall ((smt__CONSTANT__g__ Idv) (smt__a Idv) (smt__x Idv))
      (!
        (=> (smt__TLA____Mem smt__x smt__a)
          (=
            (smt__TLA____FunApp
              (smt__TLA____FunFcn__flatnd__3 smt__a smt__CONSTANT__g__)
              smt__x)
            (ite (= smt__x (smt__TLA____Cast__Int 0))
              (smt__TLA____Cast__Int 1)
              (smt__TLA____IntTimes smt__x
                (smt__TLA____FunApp smt__CONSTANT__g__
                  (smt__TLA____IntMinus smt__x (smt__TLA____Cast__Int 1)))))))
        :pattern ((smt__TLA____FunApp
                    (smt__TLA____FunFcn__flatnd__3 smt__a smt__CONSTANT__g__)
                    smt__x))
        :pattern ((smt__TLA____Mem smt__x smt__a)
                   (smt__TLA____FunFcn__flatnd__3 smt__a smt__CONSTANT__g__))))
    :named |FunAppDef TLA__FunFcn_flatnd_3|))

(declare-fun smt__TLA____Choose__flatnd__4 () Idv)

;; Axiom: ChooseDef TLA__Choose_flatnd_4
(assert
  (!
    (forall ((smt__x Idv))
      (=>
        (= smt__x (smt__TLA____FunFcn__flatnd__3 smt__TLA____NatSet smt__x))
        (= smt__TLA____Choose__flatnd__4
          (smt__TLA____FunFcn__flatnd__3 smt__TLA____NatSet
            smt__TLA____Choose__flatnd__4))))
    :named |ChooseDef TLA__Choose_flatnd_4|))

;; Goal
(assert
  (! (not (= smt__TLA____Choose__flatnd__2 smt__TLA____Choose__flatnd__4))
    :named |Goal|))

(check-sat)
(exit)
