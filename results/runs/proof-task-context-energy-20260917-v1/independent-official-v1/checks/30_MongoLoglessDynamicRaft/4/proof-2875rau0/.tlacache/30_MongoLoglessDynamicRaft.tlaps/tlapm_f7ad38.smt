;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Server_,
;;	       NEW CONSTANT CONSTANT_Secondary_,
;;	       NEW CONSTANT CONSTANT_Primary_,
;;	       NEW CONSTANT CONSTANT_Nil_,
;;	       NEW CONSTANT CONSTANT_InitTerm_,
;;	       NEW VARIABLE VARIABLE_currentTerm_,
;;	       NEW VARIABLE VARIABLE_state_,
;;	       NEW VARIABLE VARIABLE_configVersion_,
;;	       NEW VARIABLE VARIABLE_configTerm_,
;;	       NEW VARIABLE VARIABLE_config_,
;;	       NEW CONSTANT CONSTANT_MaxTerm_,
;;	       NEW CONSTANT CONSTANT_MaxLogLen_,
;;	       NEW CONSTANT CONSTANT_MaxConfigVersion_,
;;	       \A CONSTANT_S_, CONSTANT_T_ :
;;	          (\A CONSTANT_x_ :
;;	              CONSTANT_x_ \in CONSTANT_S_ <=> CONSTANT_x_ \in CONSTANT_T_)
;;	          => CONSTANT_S_ = CONSTANT_T_ 
;;	PROVE  STATE_IndAuto_ /\ ACTION_Next_ => ?h325d8
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./30_MongoLoglessDynamicRaft.tla", line 248, characters 1-2

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Anon__OPAQUE__h325d8 () Idv)

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

(declare-fun smt__CONSTANT__IsFiniteSet__ (Idv) Idv)

(declare-fun smt__CONSTANT__Cardinality__ (Idv) Idv)

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_EnabledWrapper_' (second-order)

; omitted declaration of 'CONSTANT_CdotWrapper_' (second-order)

; omitted declaration of 'CONSTANT_MapThenFoldSet_' (second-order)

(declare-fun smt__CONSTANT__Restrict__ (Idv Idv) Idv)

; omitted declaration of 'CONSTANT_RestrictDomain_' (second-order)

; omitted declaration of 'CONSTANT_RestrictValues_' (second-order)

(declare-fun smt__CONSTANT__IsRestriction__ (Idv Idv) Idv)

(declare-fun smt__CONSTANT__Range__ (Idv) Idv)

; omitted declaration of 'CONSTANT_Pointwise_' (second-order)

(declare-fun smt__CONSTANT__Inverse__ (Idv Idv Idv) Idv)

(declare-fun smt__CONSTANT__AntiFunction__ (Idv) Idv)

(declare-fun smt__CONSTANT__IsInjective__ (Idv) Idv)

(declare-fun smt__CONSTANT__Injection__ (Idv Idv) Idv)

(declare-fun smt__CONSTANT__Surjection__ (Idv Idv) Idv)

(declare-fun smt__CONSTANT__Bijection__ (Idv Idv) Idv)

(declare-fun smt__CONSTANT__ExistsInjection__ (Idv Idv) Idv)

(declare-fun smt__CONSTANT__ExistsSurjection__ (Idv Idv) Idv)

(declare-fun smt__CONSTANT__ExistsBijection__ (Idv Idv) Idv)

; omitted declaration of 'CONSTANT_FoldFunctionOnSet_' (second-order)

; omitted declaration of 'CONSTANT_FoldFunction_' (second-order)

(declare-fun smt__CONSTANT__SumFunctionOnSet__ (Idv Idv) Idv)

(declare-fun smt__CONSTANT__SumFunction__ (Idv) Idv)

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_NatInductiveDefHypothesis_' (second-order)

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

(declare-fun smt__CONSTANT__IsTransitivelyClosedOn__ (Idv Idv) Idv)

(declare-fun smt__CONSTANT__IsWellFoundedOn__ (Idv Idv) Idv)

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__CONSTANT__SetLessThan__ (Idv Idv Idv) Idv)

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_WFDefOn_' (second-order)

; omitted declaration of 'CONSTANT_OpDefinesFcn_' (second-order)

; omitted declaration of 'CONSTANT_WFInductiveDefines_' (second-order)

; omitted declaration of 'CONSTANT_WFInductiveUnique_' (second-order)

; hidden fact

; hidden fact

(declare-fun smt__CONSTANT__TransitiveClosureOn__ (Idv Idv) Idv)

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_OpToRel_' (second-order)

; hidden fact

; omitted declaration of 'CONSTANT_PreImage_' (second-order)

; hidden fact

(declare-fun smt__CONSTANT__LexPairOrdering__ (Idv Idv Idv Idv) Idv)

; hidden fact

(declare-fun smt__CONSTANT__LexProductOrdering__ (Idv Idv Idv) Idv)

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__CONSTANT__FiniteSubsetsOf__ (Idv) Idv)

(declare-fun smt__CONSTANT__StrictSubsetOrdering__ (Idv) Idv)

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__CONSTANT__Server__ () Idv)

(declare-fun smt__CONSTANT__Secondary__ () Idv)

(declare-fun smt__CONSTANT__Primary__ () Idv)

(declare-fun smt__CONSTANT__Nil__ () Idv)

(declare-fun smt__CONSTANT__InitTerm__ () Idv)

(declare-fun smt__VARIABLE__currentTerm__ () Idv)

(declare-fun smt__VARIABLE__currentTerm____prime () Idv)

(declare-fun smt__VARIABLE__state__ () Idv)

(declare-fun smt__VARIABLE__state____prime () Idv)

(declare-fun smt__VARIABLE__configVersion__ () Idv)

(declare-fun smt__VARIABLE__configVersion____prime () Idv)

(declare-fun smt__VARIABLE__configTerm__ () Idv)

(declare-fun smt__VARIABLE__configTerm____prime () Idv)

(declare-fun smt__VARIABLE__config__ () Idv)

(declare-fun smt__VARIABLE__config____prime () Idv)

(declare-fun smt__STATE__vars__ () Idv)

(declare-fun smt__CONSTANT__Quorums__ (Idv) Idv)

(declare-fun smt__STATE__QuorumsAt__ (Idv) Idv)

(declare-fun smt__CONSTANT__Empty__ (Idv) Idv)

(declare-fun smt__STATE__IsNewerConfig__ (Idv Idv) Idv)

(declare-fun smt__STATE__IsNewerOrEqualConfig__ (Idv Idv) Idv)

(declare-fun smt__CONSTANT__NewerConfig__ (Idv Idv) Idv)

(declare-fun smt__CONSTANT__NewerOrEqualConfig__ (Idv Idv) Idv)

(declare-fun smt__STATE__CanVoteForConfig__ (Idv Idv Idv) Idv)

(declare-fun smt__CONSTANT__QuorumsOverlap__ (Idv Idv) Idv)

(declare-fun smt__STATE__ConfigIsCommitted__ (Idv) Idv)

(declare-fun smt__ACTION__UpdateTermsExpr__ (Idv Idv) Idv)

(declare-fun smt__ACTION__UpdateTerms__ (Idv Idv) Idv)

(declare-fun smt__ACTION__BecomeLeader__ (Idv Idv) Idv)

(declare-fun smt__ACTION__Reconfig__ (Idv Idv) Idv)

(declare-fun smt__ACTION__SendConfig__ (Idv Idv) Idv)

(declare-fun smt__STATE__Init__ () Idv)

(declare-fun smt__ACTION__ReconfigAction__ () Idv)

(declare-fun smt__ACTION__SendConfigAction__ () Idv)

(declare-fun smt__ACTION__BecomeLeaderAction__ () Idv)

(declare-fun smt__ACTION__UpdateTermsAction__ () Idv)

(declare-fun smt__ACTION__Next__ () Idv)

(declare-fun smt__TEMPORAL__Spec__ () Idv)

(declare-fun smt__STATE__CV__ (Idv) Idv)

(declare-fun smt__STATE__ConfigDisabled__ (Idv) Idv)

(declare-fun smt__STATE__OnePrimaryPerTerm__ () Idv)

(declare-fun smt__STATE__Safety__ () Idv)

(declare-fun smt__CONSTANT__MaxTerm__ () Idv)

(declare-fun smt__CONSTANT__MaxLogLen__ () Idv)

(declare-fun smt__CONSTANT__MaxConfigVersion__ () Idv)

(declare-fun smt__CONSTANT__SeqOf__ (Idv Idv) Idv)

(declare-fun smt__CONSTANT__BoundedSeq__ (Idv Idv) Idv)

(declare-fun smt__CONSTANT__NatFinite__ () Idv)

(declare-fun smt__CONSTANT__PositiveNat__ () Idv)

(declare-fun smt__CONSTANT__NumRandSubsets__ () Idv)

(declare-fun smt__STATE__TypeOK__ () Idv)

(declare-fun smt__STATE__StateConstraint__ () Idv)

(declare-fun smt__STATE__NextUnchanged__ () Idv)

(declare-fun smt__CONSTANT__Symmetry__ () Idv)

(declare-fun smt__CONSTANT__Test__ () Idv)

(declare-fun smt__STATE__Inv2973__1__1__def__ () Idv)

(declare-fun smt__STATE__Inv1758__1__0__def__ () Idv)

(declare-fun smt__STATE__Inv3915__1__1__def__ () Idv)

(declare-fun smt__STATE__Inv3246__1__2__def__ () Idv)

(declare-fun smt__STATE__Inv866__1__0__def__ () Idv)

(declare-fun smt__STATE__IndAuto__ () Idv)

(declare-fun smt__STATE__ActiveConfigSet__ () Idv)

(declare-fun smt__CONSTANT__Inv862__1__0__def__ () Idv)

(declare-fun smt__CONSTANT__Inv846__1__0__def__ () Idv)

(declare-fun smt__CONSTANT__Inv6243__1__1__def__ () Idv)

(declare-fun smt__CONSTANT__Inv648__1__0__def__ () Idv)

(declare-fun smt__CONSTANT__Inv1925__1__1__def__ () Idv)

(declare-fun smt__CONSTANT__Inv716__1__1__def__ () Idv)

(declare-fun smt__CONSTANT__Inv852__1__2__def__ () Idv)

; hidden fact

; hidden fact

; hidden fact

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
        (and (= smt__STATE__IndAuto__ smt__TLA____Tt__Idv)
          (= smt__ACTION__Next__ smt__TLA____Tt__Idv))
        (= smt__TLA____Anon__OPAQUE__h325d8 smt__TLA____Tt__Idv)))
    :named |Goal|))

(check-sat)
(exit)
