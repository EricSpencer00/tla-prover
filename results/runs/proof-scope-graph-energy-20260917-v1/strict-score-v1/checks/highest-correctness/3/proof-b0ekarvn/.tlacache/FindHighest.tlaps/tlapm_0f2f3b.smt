;; Proof obligation:
;;	ASSUME NEW VARIABLE VARIABLE_f_,
;;	       NEW VARIABLE VARIABLE_h_,
;;	       NEW VARIABLE VARIABLE_i_,
;;	       NEW VARIABLE VARIABLE_pc_,
;;	       TEMPORAL_Spec_ => ?hcfd7e ,
;;	       TEMPORAL_Spec_ => ?h3c578 ,
;;	       TEMPORAL_Spec_ => ?h18d1b ,
;;	       \A CONSTANT_S_, CONSTANT_T_ :
;;	          (\A CONSTANT_x_ :
;;	              CONSTANT_x_ \in CONSTANT_S_ <=> CONSTANT_x_ \in CONSTANT_T_)
;;	          => CONSTANT_S_ = CONSTANT_T_ 
;;	PROVE  STATE_TypeOK_ /\ STATE_InductiveInvariant_ /\ STATE_DoneIndexValue_
;;	       => STATE_Correctness_
;; TLA+ Proof Manager 80172c6
;; Proof obligation #45
;; Generated from file "./FindHighest.tla", line 145, characters 3-4

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Anon__OPAQUE__h18d1b () Idv)

(declare-fun smt__TLA____Anon__OPAQUE__h3c578 () Idv)

(declare-fun smt__TLA____Anon__OPAQUE__hcfd7e () Idv)

(declare-fun smt__TLA____Mem (Idv Idv) Bool)

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

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_EnabledWrapper_' (second-order)

; omitted declaration of 'CONSTANT_CdotWrapper_' (second-order)

(declare-fun smt__VARIABLE__f__ () Idv)

(declare-fun smt__VARIABLE__f____prime () Idv)

(declare-fun smt__VARIABLE__h__ () Idv)

(declare-fun smt__VARIABLE__h____prime () Idv)

(declare-fun smt__VARIABLE__i__ () Idv)

(declare-fun smt__VARIABLE__i____prime () Idv)

(declare-fun smt__VARIABLE__pc__ () Idv)

(declare-fun smt__VARIABLE__pc____prime () Idv)

(declare-fun smt__CONSTANT__max__ (Idv Idv) Idv)

(declare-fun smt__STATE__vars__ () Idv)

(declare-fun smt__STATE__Init__ () Idv)

(declare-fun smt__ACTION__lb__ () Idv)

(declare-fun smt__ACTION__Terminating__ () Idv)

(declare-fun smt__ACTION__Next__ () Idv)

(declare-fun smt__TEMPORAL__Spec__ () Idv)

(declare-fun smt__STATE__Termination__ () Idv)

(declare-fun smt__STATE__TypeOK__ () Idv)

; hidden fact

(declare-fun smt__STATE__InductiveInvariant__ () Idv)

; hidden fact

(declare-fun smt__STATE__DoneIndexValue__ () Idv)

; hidden fact

(declare-fun smt__STATE__Correctness__ () Idv)

; hidden fact

; hidden fact

(assert
  (=> (= smt__TEMPORAL__Spec__ smt__TLA____Tt__Idv)
    (= smt__TLA____Anon__OPAQUE__hcfd7e smt__TLA____Tt__Idv)))

(assert
  (=> (= smt__TEMPORAL__Spec__ smt__TLA____Tt__Idv)
    (= smt__TLA____Anon__OPAQUE__h3c578 smt__TLA____Tt__Idv)))

(assert
  (=> (= smt__TEMPORAL__Spec__ smt__TLA____Tt__Idv)
    (= smt__TLA____Anon__OPAQUE__h18d1b smt__TLA____Tt__Idv)))

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
      (=>
        (and
          (and (= smt__STATE__TypeOK__ smt__TLA____Tt__Idv)
            (= smt__STATE__InductiveInvariant__ smt__TLA____Tt__Idv))
          (= smt__STATE__DoneIndexValue__ smt__TLA____Tt__Idv))
        (= smt__STATE__Correctness__ smt__TLA____Tt__Idv))) :named |Goal|))

(check-sat)
(exit)
