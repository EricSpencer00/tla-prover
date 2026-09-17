;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_N_,
;;	       NEW VARIABLE VARIABLE_x_,
;;	       NEW VARIABLE VARIABLE_y_,
;;	       NEW VARIABLE VARIABLE_pc_
;;	PROVE  (/\ VARIABLE_x_ = [CONSTANT_i_ \in 0..CONSTANT_N_ - 1 |-> 0]
;;	        /\ VARIABLE_y_ = [CONSTANT_i_ \in 0..CONSTANT_N_ - 1 |-> 0]
;;	        /\ VARIABLE_pc_ = [CONSTANT_self_ \in 0..CONSTANT_N_ - 1 |-> "a"])
;;	       /\ ?h5d897 => ?hbd6e2
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./Simple.tla", line 127, characters 1-2

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Anon__OPAQUE__h5d897 () Idv)

(declare-fun smt__TLA____Anon__OPAQUE__hbd6e2 () Idv)

(declare-fun smt__TLA____Cast__Int (Int) Idv)

(declare-fun smt__TLA____FunApp (Idv Idv) Idv)

(declare-fun smt__TLA____FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA____FunIsafcn (Idv) Bool)

(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)

(declare-fun smt__TLA____IntMinus (Idv Idv) Idv)

(declare-fun smt__TLA____IntRange (Idv Idv) Idv)

(declare-fun smt__TLA____IntSet () Idv)

(declare-fun smt__TLA____Mem (Idv Idv) Bool)

(declare-fun smt__TLA____Proj__Int (Idv) Int)

(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLA____StrLit__a () Idv)

(declare-fun smt__TLA____StrSet () Idv)

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

;; Axiom: StrLitIsstr a
(assert
  (! (smt__TLA____Mem smt__TLA____StrLit__a smt__TLA____StrSet)
    :named |StrLitIsstr a|))

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

(declare-fun smt__CONSTANT__N__ () Idv)

; hidden fact

(declare-fun smt__VARIABLE__x__ () Idv)

(declare-fun smt__VARIABLE__x____prime () Idv)

(declare-fun smt__VARIABLE__y__ () Idv)

(declare-fun smt__VARIABLE__y____prime () Idv)

(declare-fun smt__VARIABLE__pc__ () Idv)

(declare-fun smt__VARIABLE__pc____prime () Idv)

(declare-fun smt__TLA____FunFcn__flatnd__1 (Idv) Idv)

;; Axiom: FunConstrIsafcn TLA__FunFcn_flatnd_1
(assert
  (!
    (forall ((smt__a Idv))
      (! (smt__TLA____FunIsafcn (smt__TLA____FunFcn__flatnd__1 smt__a))
        :pattern ((smt__TLA____FunFcn__flatnd__1 smt__a))))
    :named |FunConstrIsafcn TLA__FunFcn_flatnd_1|))

;; Axiom: FunDomDef TLA__FunFcn_flatnd_1
(assert
  (!
    (forall ((smt__a Idv))
      (!
        (= (smt__TLA____FunDom (smt__TLA____FunFcn__flatnd__1 smt__a)) smt__a)
        :pattern ((smt__TLA____FunFcn__flatnd__1 smt__a))))
    :named |FunDomDef TLA__FunFcn_flatnd_1|))

;; Axiom: FunAppDef TLA__FunFcn_flatnd_1
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (=> (smt__TLA____Mem smt__x smt__a)
          (=
            (smt__TLA____FunApp (smt__TLA____FunFcn__flatnd__1 smt__a) smt__x)
            (smt__TLA____Cast__Int 0)))
        :pattern ((smt__TLA____FunApp (smt__TLA____FunFcn__flatnd__1 smt__a)
                    smt__x))
        :pattern ((smt__TLA____Mem smt__x smt__a)
                   (smt__TLA____FunFcn__flatnd__1 smt__a))))
    :named |FunAppDef TLA__FunFcn_flatnd_1|))

(declare-fun smt__TLA____FunFcn__flatnd__3 (Idv) Idv)

;; Axiom: FunConstrIsafcn TLA__FunFcn_flatnd_3
(assert
  (!
    (forall ((smt__a Idv))
      (! (smt__TLA____FunIsafcn (smt__TLA____FunFcn__flatnd__3 smt__a))
        :pattern ((smt__TLA____FunFcn__flatnd__3 smt__a))))
    :named |FunConstrIsafcn TLA__FunFcn_flatnd_3|))

;; Axiom: FunDomDef TLA__FunFcn_flatnd_3
(assert
  (!
    (forall ((smt__a Idv))
      (!
        (= (smt__TLA____FunDom (smt__TLA____FunFcn__flatnd__3 smt__a)) smt__a)
        :pattern ((smt__TLA____FunFcn__flatnd__3 smt__a))))
    :named |FunDomDef TLA__FunFcn_flatnd_3|))

;; Axiom: FunAppDef TLA__FunFcn_flatnd_3
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (=> (smt__TLA____Mem smt__x smt__a)
          (=
            (smt__TLA____FunApp (smt__TLA____FunFcn__flatnd__3 smt__a) smt__x)
            smt__TLA____StrLit__a))
        :pattern ((smt__TLA____FunApp (smt__TLA____FunFcn__flatnd__3 smt__a)
                    smt__x))
        :pattern ((smt__TLA____Mem smt__x smt__a)
                   (smt__TLA____FunFcn__flatnd__3 smt__a))))
    :named |FunAppDef TLA__FunFcn_flatnd_3|))

;; Goal
(assert
  (!
    (not
      (=>
        (and
          (and
            (= smt__VARIABLE__x__
              (smt__TLA____FunFcn__flatnd__1
                (smt__TLA____IntRange (smt__TLA____Cast__Int 0)
                  (smt__TLA____IntMinus smt__CONSTANT__N__
                    (smt__TLA____Cast__Int 1)))))
            (= smt__VARIABLE__y__
              (smt__TLA____FunFcn__flatnd__1
                (smt__TLA____IntRange (smt__TLA____Cast__Int 0)
                  (smt__TLA____IntMinus smt__CONSTANT__N__
                    (smt__TLA____Cast__Int 1)))))
            (= smt__VARIABLE__pc__
              (smt__TLA____FunFcn__flatnd__3
                (smt__TLA____IntRange (smt__TLA____Cast__Int 0)
                  (smt__TLA____IntMinus smt__CONSTANT__N__
                    (smt__TLA____Cast__Int 1))))))
          (= smt__TLA____Anon__OPAQUE__h5d897 smt__TLA____Tt__Idv))
        (= smt__TLA____Anon__OPAQUE__hbd6e2 smt__TLA____Tt__Idv)))
    :named |Goal|))

(check-sat)
(exit)
