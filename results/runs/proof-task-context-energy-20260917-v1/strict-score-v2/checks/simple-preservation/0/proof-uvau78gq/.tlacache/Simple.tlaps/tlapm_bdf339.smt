;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_N_,
;;	       NEW VARIABLE VARIABLE_x_,
;;	       NEW VARIABLE VARIABLE_y_,
;;	       NEW VARIABLE VARIABLE_pc_,
;;	       CONSTANT_N_ \in Nat /\ CONSTANT_N_ > 0 
;;	PROVE  STATE_Inv_ /\ (ACTION_Next_ \/ ?h6fbaa = STATE_vars_) => ?hdb2fe
;; TLA+ Proof Manager 80172c6
;; Proof obligation #8
;; Generated from file "./Simple.tla", line 131, characters 3-4

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Anon__OPAQUE__h6fbaa () Idv)

(declare-fun smt__TLA____Anon__OPAQUE__hdb2fe () Idv)

(declare-fun smt__TLA____Cast__Int (Int) Idv)

(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)

(declare-fun smt__TLA____IntSet () Idv)

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

(declare-fun smt__STATE__vars__ () Idv)

(declare-fun smt__CONSTANT__ProcSet__ () Idv)

(declare-fun smt__STATE__Init__ () Idv)

(declare-fun smt__ACTION__a__ (Idv) Idv)

(declare-fun smt__ACTION__b__ (Idv) Idv)

(declare-fun smt__ACTION__proc__ (Idv) Idv)

(declare-fun smt__ACTION__Terminating__ () Idv)

(declare-fun smt__ACTION__Next__ () Idv)

(declare-fun smt__TEMPORAL__Spec__ () Idv)

(declare-fun smt__STATE__Termination__ () Idv)

(declare-fun smt__STATE__PCorrect__ () Idv)

(declare-fun smt__STATE__TypeOK__ () Idv)

(declare-fun smt__STATE__Inv__ () Idv)

(assert
  (and (smt__TLA____Mem smt__CONSTANT__N__ smt__TLA____NatSet)
    (and (smt__TLA____IntLteq (smt__TLA____Cast__Int 0) smt__CONSTANT__N__)
      (distinct (smt__TLA____Cast__Int 0) smt__CONSTANT__N__))))

; hidden fact

; hidden fact

; hidden fact

;; Goal
(assert
  (!
    (not
      (=>
        (and (= smt__STATE__Inv__ smt__TLA____Tt__Idv)
          (or (= smt__ACTION__Next__ smt__TLA____Tt__Idv)
            (= smt__TLA____Anon__OPAQUE__h6fbaa smt__STATE__vars__)))
        (= smt__TLA____Anon__OPAQUE__hdb2fe smt__TLA____Tt__Idv)))
    :named |Goal|))

(check-sat)
(exit)
