;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Node_,
;;	       NEW CONSTANT CONSTANT_Quorum_,
;;	       NEW CONSTANT CONSTANT_Value_,
;;	       NEW VARIABLE VARIABLE_vote_request_msg_,
;;	       NEW VARIABLE VARIABLE_voted_,
;;	       NEW VARIABLE VARIABLE_vote_msg_,
;;	       NEW VARIABLE VARIABLE_votes_,
;;	       NEW VARIABLE VARIABLE_leader_,
;;	       NEW VARIABLE VARIABLE_decided_,
;;	       \A CONSTANT_S_, CONSTANT_T_ :
;;	          (\A CONSTANT_x_ :
;;	              CONSTANT_x_ \in CONSTANT_S_ <=> CONSTANT_x_ \in CONSTANT_T_)
;;	          => CONSTANT_S_ = CONSTANT_T_ 
;;	PROVE  STATE_IndAuto_ /\ ACTION_Next_ => ?h325d8
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./29_consensus_epr.tla", line 153, characters 53-54

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

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_EnabledWrapper_' (second-order)

; omitted declaration of 'CONSTANT_CdotWrapper_' (second-order)

(declare-fun smt__CONSTANT__Node__ () Idv)

(declare-fun smt__CONSTANT__Quorum__ () Idv)

(declare-fun smt__CONSTANT__Value__ () Idv)

(declare-fun smt__VARIABLE__vote__request__msg__ () Idv)

(declare-fun smt__VARIABLE__vote__request__msg____prime () Idv)

(declare-fun smt__VARIABLE__voted__ () Idv)

(declare-fun smt__VARIABLE__voted____prime () Idv)

(declare-fun smt__VARIABLE__vote__msg__ () Idv)

(declare-fun smt__VARIABLE__vote__msg____prime () Idv)

(declare-fun smt__VARIABLE__votes__ () Idv)

(declare-fun smt__VARIABLE__votes____prime () Idv)

(declare-fun smt__VARIABLE__leader__ () Idv)

(declare-fun smt__VARIABLE__leader____prime () Idv)

(declare-fun smt__VARIABLE__decided__ () Idv)

(declare-fun smt__VARIABLE__decided____prime () Idv)

(declare-fun smt__STATE__vars__ () Idv)

(declare-fun smt__ACTION__SendRequestVote__ (Idv Idv) Idv)

(declare-fun smt__ACTION__SendVote__ (Idv Idv) Idv)

(declare-fun smt__ACTION__RecvVote__ (Idv Idv) Idv)

(declare-fun smt__ACTION__BecomeLeader__ (Idv Idv) Idv)

(declare-fun smt__ACTION__Decide__ (Idv Idv) Idv)

(declare-fun smt__STATE__Init__ () Idv)

(declare-fun smt__ACTION__Next__ () Idv)

(declare-fun smt__CONSTANT__Symmetry__ () Idv)

(declare-fun smt__STATE__TypeOK__ () Idv)

(declare-fun smt__STATE__Safety__ () Idv)

(declare-fun smt__STATE__SafetyWithTypeOK__ () Idv)

(declare-fun smt__STATE__NextUnchanged__ () Idv)

(declare-fun smt__STATE__Inv119__1__0__def__ () Idv)

(declare-fun smt__STATE__Inv152__1__1__def__ () Idv)

(declare-fun smt__STATE__Inv693__1__2__def__ () Idv)

(declare-fun smt__STATE__Inv164__1__3__def__ () Idv)

(declare-fun smt__STATE__Inv622__1__4__def__ () Idv)

(declare-fun smt__STATE__Inv4302__2__0__def__ () Idv)

(declare-fun smt__STATE__Inv5288__2__0__def__ () Idv)

(declare-fun smt__STATE__IndAuto__ () Idv)

; hidden fact

; hidden fact

; hidden fact

; hidden fact

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
