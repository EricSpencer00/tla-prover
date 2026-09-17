;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Node_,
;;	       NEW CONSTANT CONSTANT_Quorum_,
;;	       NEW CONSTANT CONSTANT_Value_,
;;	       NEW VARIABLE VARIABLE_voted_,
;;	       NEW VARIABLE VARIABLE_vote_,
;;	       NEW VARIABLE VARIABLE_decided_,
;;	       ASSUME NEW CONSTANT CONSTANT_S_,
;;	              CONSTANT_IsFiniteSet_(CONSTANT_S_) ,
;;	              NEW CONSTANT CONSTANT_T_ \in SUBSET CONSTANT_S_
;;	       PROVE  /\ CONSTANT_IsFiniteSet_(CONSTANT_T_)
;;	              /\ CONSTANT_Cardinality_(CONSTANT_T_)
;;	                 =< CONSTANT_Cardinality_(CONSTANT_S_)
;;	              /\ CONSTANT_Cardinality_(CONSTANT_S_)
;;	                 = CONSTANT_Cardinality_(CONSTANT_T_)
;;	                 => CONSTANT_S_ = CONSTANT_T_ ,
;;	       /\ CONSTANT_IsFiniteSet_({})
;;	       /\ \A CONSTANT_S_ :
;;	             CONSTANT_IsFiniteSet_(CONSTANT_S_)
;;	             => CONSTANT_Cardinality_(CONSTANT_S_) = 0 <=> CONSTANT_S_ = {} ,
;;	       CONSTANT_Cardinality_({}) = 0 
;;	PROVE  STATE_IndAuto_ /\ ACTION_Next_ => ?h325d8
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./23_toy_consensus_epr.tla", line 74, characters 53-54

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Anon__OPAQUE__h325d8 () Idv)

(declare-fun smt__TLA____Cast__Int (Int) Idv)

(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)

(declare-fun smt__TLA____IntSet () Idv)

(declare-fun smt__TLA____Mem (Idv Idv) Bool)

(declare-fun smt__TLA____Proj__Int (Idv) Int)

(declare-fun smt__TLA____SetEnum__0 () Idv)

(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLA____Subset (Idv) Idv)

(declare-fun smt__TLA____SubsetEq (Idv Idv) Bool)

(declare-fun smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (Idv
  Idv) Bool)

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

;; Axiom: SubsetEqIntro
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=>
          (forall ((smt__z Idv))
            (=> (smt__TLA____Mem smt__z smt__x)
              (smt__TLA____Mem smt__z smt__y)))
          (smt__TLA____SubsetEq smt__x smt__y))
        :pattern ((smt__TLA____SubsetEq smt__x smt__y))))
    :named |SubsetEqIntro|))

;; Axiom: SubsetEqElim
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv) (smt__z Idv))
      (!
        (=>
          (and (smt__TLA____SubsetEq smt__x smt__y)
            (smt__TLA____Mem smt__z smt__x)) (smt__TLA____Mem smt__z smt__y))
        :pattern ((smt__TLA____SubsetEq smt__x smt__y)
                   (smt__TLA____Mem smt__z smt__x)))) :named |SubsetEqElim|))

;; Axiom: SubsetDefAlt
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (= (smt__TLA____Mem smt__x (smt__TLA____Subset smt__a))
          (smt__TLA____SubsetEq smt__x smt__a))
        :pattern ((smt__TLA____Mem smt__x (smt__TLA____Subset smt__a)))
        :pattern ((smt__TLA____SubsetEq smt__x smt__a)
                   (smt__TLA____Subset smt__a)))) :named |SubsetDefAlt|))

;; Axiom: EnumDefElim 0
(assert
  (!
    (forall ((smt__x Idv))
      (! (not (smt__TLA____Mem smt__x smt__TLA____SetEnum__0))
        :pattern ((smt__TLA____Mem smt__x smt__TLA____SetEnum__0))))
    :named |EnumDefElim 0|))

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

;; Axiom: ExtTrigEqDef Set$Idv$
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (= (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y)
          (= smt__x smt__y))
        :pattern ((smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ 
                    smt__x smt__y)))) :named |ExtTrigEqDef Set$Idv$|))

;; Axiom: ExtTrigEqTrigger Idv
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (! (smt__TLA____SetExtTrigger smt__x smt__y)
        :pattern ((smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ 
                    smt__x smt__y)))) :named |ExtTrigEqTrigger Idv|))

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

(declare-fun smt__CONSTANT__Node__ () Idv)

(declare-fun smt__CONSTANT__Quorum__ () Idv)

(declare-fun smt__CONSTANT__Value__ () Idv)

(declare-fun smt__VARIABLE__voted__ () Idv)

(declare-fun smt__VARIABLE__voted____prime () Idv)

(declare-fun smt__VARIABLE__vote__ () Idv)

(declare-fun smt__VARIABLE__vote____prime () Idv)

(declare-fun smt__VARIABLE__decided__ () Idv)

(declare-fun smt__VARIABLE__decided____prime () Idv)

(declare-fun smt__STATE__vars__ () Idv)

(declare-fun smt__STATE__ChosenAt__ (Idv Idv) Idv)

(declare-fun smt__ACTION__CastVote__ (Idv Idv) Idv)

(declare-fun smt__ACTION__Decide__ (Idv Idv) Idv)

(declare-fun smt__STATE__Init__ () Idv)

(declare-fun smt__ACTION__Next__ () Idv)

(declare-fun smt__STATE__NextUnchanged__ () Idv)

(declare-fun smt__STATE__TypeOK__ () Idv)

(declare-fun smt__STATE__Safety__ () Idv)

(declare-fun smt__CONSTANT__Symmetry__ () Idv)

(declare-fun smt__STATE__Inv220__1__0__def__ () Idv)

(declare-fun smt__STATE__Inv155__1__1__def__ () Idv)

(declare-fun smt__STATE__Inv201__2__2__def__ () Idv)

(declare-fun smt__STATE__IndAuto__ () Idv)

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(assert
  (forall ((smt__CONSTANT__S__ Idv))
    (=>
      (= (smt__CONSTANT__IsFiniteSet__ smt__CONSTANT__S__)
        smt__TLA____Tt__Idv)
      (forall ((smt__CONSTANT__T__ Idv))
        (=>
          (smt__TLA____Mem smt__CONSTANT__T__
            (smt__TLA____Subset smt__CONSTANT__S__))
          (and
            (= (smt__CONSTANT__IsFiniteSet__ smt__CONSTANT__T__)
              smt__TLA____Tt__Idv)
            (smt__TLA____IntLteq
              (smt__CONSTANT__Cardinality__ smt__CONSTANT__T__)
              (smt__CONSTANT__Cardinality__ smt__CONSTANT__S__))
            (=>
              (= (smt__CONSTANT__Cardinality__ smt__CONSTANT__S__)
                (smt__CONSTANT__Cardinality__ smt__CONSTANT__T__))
              (= smt__CONSTANT__S__ smt__CONSTANT__T__))))))))

(assert
  (and
    (= (smt__CONSTANT__IsFiniteSet__ smt__TLA____SetEnum__0)
      smt__TLA____Tt__Idv)
    (forall ((smt__CONSTANT__S__ Idv))
      (=>
        (= (smt__CONSTANT__IsFiniteSet__ smt__CONSTANT__S__)
          smt__TLA____Tt__Idv)
        (=
          (= (smt__CONSTANT__Cardinality__ smt__CONSTANT__S__)
            (smt__TLA____Cast__Int 0))
          (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__
            smt__CONSTANT__S__ smt__TLA____SetEnum__0))))))

(assert
  (= (smt__CONSTANT__Cardinality__ smt__TLA____SetEnum__0)
    (smt__TLA____Cast__Int 0)))

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
