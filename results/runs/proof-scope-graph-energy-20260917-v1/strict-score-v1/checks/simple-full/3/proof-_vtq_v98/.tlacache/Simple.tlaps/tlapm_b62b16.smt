;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_N_,
;;	       NEW VARIABLE VARIABLE_x_,
;;	       NEW VARIABLE VARIABLE_y_,
;;	       NEW VARIABLE VARIABLE_pc_,
;;	       \A CONSTANT_S_, CONSTANT_T_ :
;;	          (\A CONSTANT_x_ :
;;	              CONSTANT_x_ \in CONSTANT_S_ <=> CONSTANT_x_ \in CONSTANT_T_)
;;	          => CONSTANT_S_ = CONSTANT_T_ 
;;	PROVE  TEMPORAL_Spec_ => ?hda7c2
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./Simple.tla", line 127, characters 1-2

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Anon__OPAQUE__hda7c2 () Idv)

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
      (=> (= smt__TEMPORAL__Spec__ smt__TLA____Tt__Idv)
        (= smt__TLA____Anon__OPAQUE__hda7c2 smt__TLA____Tt__Idv)))
    :named |Goal|))

(check-sat)
(exit)
