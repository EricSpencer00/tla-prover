;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Node_,
;;	       NEW CONSTANT CONSTANT_Value_,
;;	       NEW CONSTANT CONSTANT_Nil_,
;;	       NEW VARIABLE VARIABLE_vote_,
;;	       NEW VARIABLE VARIABLE_voted_,
;;	       NEW VARIABLE VARIABLE_decided_
;;	PROVE  (/\ /\ VARIABLE_vote_
;;	              \in [CONSTANT_Node_ -> CONSTANT_Value_ \cup {CONSTANT_Nil_}]
;;	           /\ VARIABLE_voted_ \in [CONSTANT_Node_ -> BOOLEAN]
;;	           /\ VARIABLE_decided_ \in SUBSET CONSTANT_Value_
;;	        /\ \A CONSTANT_vi_, CONSTANT_vj_ \in VARIABLE_decided_ :
;;	              CONSTANT_vi_ = CONSTANT_vj_
;;	        /\ \A CONSTANT_s_, CONSTANT_t_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_Q_
;;	                 \in {CONSTANT_i_ \in SUBSET CONSTANT_Node_ :
;;	                        CONSTANT_Cardinality_(CONSTANT_i_) * 2
;;	                        > CONSTANT_Cardinality_(CONSTANT_Node_)} :
;;	                 \A CONSTANT_v_ \in CONSTANT_Value_ :
;;	                    \E CONSTANT_n_ \in CONSTANT_Q_ :
;;	                       VARIABLE_voted_[CONSTANT_s_]
;;	                       \/ ~VARIABLE_vote_[CONSTANT_s_] = CONSTANT_v_
;;	        /\ \A CONSTANT_s_, CONSTANT_t_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_Q_
;;	                 \in {CONSTANT_i_ \in SUBSET CONSTANT_Node_ :
;;	                        CONSTANT_Cardinality_(CONSTANT_i_) * 2
;;	                        > CONSTANT_Cardinality_(CONSTANT_Node_)} :
;;	                 \A CONSTANT_v_ \in CONSTANT_Value_ :
;;	                    \E CONSTANT_n_ \in CONSTANT_Q_ :
;;	                       VARIABLE_vote_[CONSTANT_n_] = CONSTANT_v_
;;	                       \/ ~CONSTANT_v_ \in VARIABLE_decided_)
;;	       /\ (\/ \E CONSTANT_i_ \in CONSTANT_Node_,
;;	                 CONSTANT_v_ \in CONSTANT_Value_ :
;;	                 /\ ~VARIABLE_voted_[CONSTANT_i_]
;;	                 /\ ?VARIABLE_vote_#prime
;;	                    = [VARIABLE_vote_ EXCEPT ![CONSTANT_i_] = CONSTANT_v_]
;;	                 /\ ?VARIABLE_voted_#prime
;;	                    = [VARIABLE_voted_ EXCEPT ![CONSTANT_i_] = TRUE]
;;	                 /\ ?VARIABLE_decided_#prime = VARIABLE_decided_
;;	           \/ \E CONSTANT_v_ \in CONSTANT_Value_,
;;	                 CONSTANT_Q_
;;	                 \in {CONSTANT_i_ \in SUBSET CONSTANT_Node_ :
;;	                        CONSTANT_Cardinality_(CONSTANT_i_) * 2
;;	                        > CONSTANT_Cardinality_(CONSTANT_Node_)} :
;;	                 /\ \A CONSTANT_n_ \in CONSTANT_Q_ :
;;	                       VARIABLE_vote_[CONSTANT_n_] = CONSTANT_v_
;;	                 /\ ?VARIABLE_decided_#prime
;;	                    = VARIABLE_decided_ \cup {CONSTANT_v_}
;;	                 /\ /\ ?VARIABLE_vote_#prime = VARIABLE_vote_
;;	                    /\ ?VARIABLE_voted_#prime = VARIABLE_voted_)
;;	       => (/\ /\ ?VARIABLE_vote_#prime
;;	                 \in [CONSTANT_Node_ -> CONSTANT_Value_ \cup {CONSTANT_Nil_}]
;;	              /\ ?VARIABLE_voted_#prime \in [CONSTANT_Node_ -> BOOLEAN]
;;	              /\ ?VARIABLE_decided_#prime \in SUBSET CONSTANT_Value_
;;	           /\ \A CONSTANT_vi_, CONSTANT_vj_ \in ?VARIABLE_decided_#prime :
;;	                 CONSTANT_vi_ = CONSTANT_vj_
;;	           /\ \A CONSTANT_s_, CONSTANT_t_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_Q_
;;	                    \in {CONSTANT_i_ \in SUBSET CONSTANT_Node_ :
;;	                           CONSTANT_Cardinality_(CONSTANT_i_) * 2
;;	                           > CONSTANT_Cardinality_(CONSTANT_Node_)} :
;;	                    \A CONSTANT_v_ \in CONSTANT_Value_ :
;;	                       \E CONSTANT_n_ \in CONSTANT_Q_ :
;;	                          ?VARIABLE_voted_#prime[CONSTANT_s_]
;;	                          \/ ~?VARIABLE_vote_#prime[CONSTANT_s_]
;;	                              = CONSTANT_v_
;;	           /\ \A CONSTANT_s_, CONSTANT_t_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_Q_
;;	                    \in {CONSTANT_i_ \in SUBSET CONSTANT_Node_ :
;;	                           CONSTANT_Cardinality_(CONSTANT_i_) * 2
;;	                           > CONSTANT_Cardinality_(CONSTANT_Node_)} :
;;	                    \A CONSTANT_v_ \in CONSTANT_Value_ :
;;	                       \E CONSTANT_n_ \in CONSTANT_Q_ :
;;	                          ?VARIABLE_vote_#prime[CONSTANT_n_] = CONSTANT_v_
;;	                          \/ ~CONSTANT_v_ \in ?VARIABLE_decided_#prime)
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./5_toy_consensus_forall.tla", line 99, characters 53-54

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____BoolSet () Idv)

(declare-fun smt__TLA____Cast__Bool (Bool) Idv)

(declare-fun smt__TLA____Cast__Int (Int) Idv)

(declare-fun smt__TLA____Cup (Idv Idv) Idv)

(declare-fun smt__TLA____FunApp (Idv Idv) Idv)

(declare-fun smt__TLA____FunDom (Idv) Idv)

(declare-fun smt__TLA____FunExcept (Idv Idv Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA____FunIsafcn (Idv) Bool)

(declare-fun smt__TLA____FunSet (Idv Idv) Idv)

(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)

(declare-fun smt__TLA____IntSet () Idv)

(declare-fun smt__TLA____IntTimes (Idv Idv) Idv)

(declare-fun smt__TLA____Mem (Idv Idv) Bool)

(declare-fun smt__TLA____Proj__Int (Idv) Int)

(declare-fun smt__TLA____SetEnum__0 () Idv)

(declare-fun smt__TLA____SetEnum__1 (Idv) Idv)

(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)

; omitted declaration of 'TLA__SetSt' (second-order)

(declare-fun smt__TLA____Subset (Idv) Idv)

(declare-fun smt__TLA____SubsetEq (Idv Idv) Bool)

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

;; Axiom: CupDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (= (smt__TLA____Mem smt__x (smt__TLA____Cup smt__a smt__b))
          (or (smt__TLA____Mem smt__x smt__a) (smt__TLA____Mem smt__x smt__b)))
        :pattern ((smt__TLA____Mem smt__x (smt__TLA____Cup smt__a smt__b)))
        :pattern ((smt__TLA____Mem smt__x smt__a)
                   (smt__TLA____Cup smt__a smt__b))
        :pattern ((smt__TLA____Mem smt__x smt__b)
                   (smt__TLA____Cup smt__a smt__b)))) :named |CupDef|))

; omitted fact (second-order)

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

;; Axiom: FunSetIntro
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (and (smt__TLA____FunIsafcn smt__f)
            (= (smt__TLA____FunDom smt__f) smt__a)
            (forall ((smt__x Idv))
              (=> (smt__TLA____Mem smt__x smt__a)
                (smt__TLA____Mem (smt__TLA____FunApp smt__f smt__x) smt__b))))
          (smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b)))
        :pattern ((smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b)))))
    :named |FunSetIntro|))

;; Axiom: FunSetElim1
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=> (smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b))
          (and (smt__TLA____FunIsafcn smt__f)
            (= (smt__TLA____FunDom smt__f) smt__a)))
        :pattern ((smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b)))))
    :named |FunSetElim1|))

;; Axiom: FunSetElim2
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv) (smt__x Idv))
      (!
        (=>
          (and (smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b))
            (smt__TLA____Mem smt__x smt__a))
          (smt__TLA____Mem (smt__TLA____FunApp smt__f smt__x) smt__b))
        :pattern ((smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b))
                   (smt__TLA____Mem smt__x smt__a))
        :pattern ((smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b))
                   (smt__TLA____FunApp smt__f smt__x)))) :named |FunSetElim2|))

; omitted fact (second-order)

; omitted fact (second-order)

; omitted fact (second-order)

;; Axiom: FunExceptIsafcn
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (! (smt__TLA____FunIsafcn (smt__TLA____FunExcept smt__f smt__x smt__y))
        :pattern ((smt__TLA____FunExcept smt__f smt__x smt__y))))
    :named |FunExceptIsafcn|))

;; Axiom: FunExceptDomDef
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (= (smt__TLA____FunDom (smt__TLA____FunExcept smt__f smt__x smt__y))
          (smt__TLA____FunDom smt__f))
        :pattern ((smt__TLA____FunExcept smt__f smt__x smt__y))))
    :named |FunExceptDomDef|))

;; Axiom: FunExceptAppDef1
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom smt__f))
          (=
            (smt__TLA____FunApp (smt__TLA____FunExcept smt__f smt__x smt__y)
              smt__x) smt__y))
        :pattern ((smt__TLA____FunExcept smt__f smt__x smt__y))))
    :named |FunExceptAppDef1|))

;; Axiom: FunExceptAppDef2
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv) (smt__z Idv))
      (!
        (=> (smt__TLA____Mem smt__z (smt__TLA____FunDom smt__f))
          (and
            (=> (= smt__z smt__x)
              (=
                (smt__TLA____FunApp
                  (smt__TLA____FunExcept smt__f smt__x smt__y) smt__z) 
                smt__y))
            (=> (distinct smt__z smt__x)
              (=
                (smt__TLA____FunApp
                  (smt__TLA____FunExcept smt__f smt__x smt__y) smt__z)
                (smt__TLA____FunApp smt__f smt__z)))))
        :pattern ((smt__TLA____FunApp
                    (smt__TLA____FunExcept smt__f smt__x smt__y) smt__z))
        :pattern ((smt__TLA____FunExcept smt__f smt__x smt__y)
                   (smt__TLA____FunApp smt__f smt__z))))
    :named |FunExceptAppDef2|))

; omitted fact (second-order)

;; Axiom: EnumDefIntro 1
(assert
  (!
    (forall ((smt__a1 Idv))
      (! (smt__TLA____Mem smt__a1 (smt__TLA____SetEnum__1 smt__a1))
        :pattern ((smt__TLA____SetEnum__1 smt__a1)))) :named |EnumDefIntro 1|))

;; Axiom: EnumDefElim 0
(assert
  (!
    (forall ((smt__x Idv))
      (! (not (smt__TLA____Mem smt__x smt__TLA____SetEnum__0))
        :pattern ((smt__TLA____Mem smt__x smt__TLA____SetEnum__0))))
    :named |EnumDefElim 0|))

;; Axiom: EnumDefElim 1
(assert
  (!
    (forall ((smt__a1 Idv) (smt__x Idv))
      (!
        (=> (smt__TLA____Mem smt__x (smt__TLA____SetEnum__1 smt__a1))
          (= smt__x smt__a1))
        :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetEnum__1 smt__a1)))))
    :named |EnumDefElim 1|))

;; Axiom: CastInjAlt Bool
(assert
  (!
    (and (= (smt__TLA____Cast__Bool true) smt__TLA____Tt__Idv)
      (distinct (smt__TLA____Cast__Bool false) smt__TLA____Tt__Idv))
    :named |CastInjAlt Bool|))

;; Axiom: CastInjAlt Int
(assert
  (!
    (forall ((smt__x Int))
      (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x)))
        :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))

;; Axiom: TypeGuardIntro Bool
(assert
  (!
    (forall ((smt__z Bool))
      (!
        (smt__TLA____Mem (smt__TLA____Cast__Bool smt__z) smt__TLA____BoolSet)
        :pattern ((smt__TLA____Cast__Bool smt__z))))
    :named |TypeGuardIntro Bool|))

;; Axiom: TypeGuardIntro Int
(assert
  (!
    (forall ((smt__z Int))
      (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet)
        :pattern ((smt__TLA____Cast__Int smt__z))))
    :named |TypeGuardIntro Int|))

;; Axiom: TypeGuardElim Bool
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (=> (smt__TLA____Mem smt__x smt__TLA____BoolSet)
          (or (= smt__x (smt__TLA____Cast__Bool true))
            (= smt__x (smt__TLA____Cast__Bool false))))
        :pattern ((smt__TLA____Mem smt__x smt__TLA____BoolSet))))
    :named |TypeGuardElim Bool|))

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

(declare-fun smt__CONSTANT__Value__ () Idv)

(declare-fun smt__CONSTANT__Nil__ () Idv)

(declare-fun smt__VARIABLE__vote__ () Idv)

(declare-fun smt__VARIABLE__vote____prime () Idv)

(declare-fun smt__VARIABLE__voted__ () Idv)

(declare-fun smt__VARIABLE__voted____prime () Idv)

(declare-fun smt__VARIABLE__decided__ () Idv)

(declare-fun smt__VARIABLE__decided____prime () Idv)

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__TLA____SetSt__flatnd__1 (Idv) Idv)

;; Axiom: SetStDef TLA__SetSt_flatnd_1
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (= (smt__TLA____Mem smt__x (smt__TLA____SetSt__flatnd__1 smt__a))
          (and (smt__TLA____Mem smt__x smt__a)
            (and
              (smt__TLA____IntLteq
                (smt__CONSTANT__Cardinality__ smt__CONSTANT__Node__)
                (smt__TLA____IntTimes (smt__CONSTANT__Cardinality__ smt__x)
                  (smt__TLA____Cast__Int 2)))
              (distinct (smt__CONSTANT__Cardinality__ smt__CONSTANT__Node__)
                (smt__TLA____IntTimes (smt__CONSTANT__Cardinality__ smt__x)
                  (smt__TLA____Cast__Int 2))))))
        :pattern ((smt__TLA____Mem smt__x
                    (smt__TLA____SetSt__flatnd__1 smt__a)))
        :pattern ((smt__TLA____Mem smt__x smt__a)
                   (smt__TLA____SetSt__flatnd__1 smt__a))))
    :named |SetStDef TLA__SetSt_flatnd_1|))

;; Goal
(assert
  (!
    (not
      (=>
        (and
          (and
            (and
              (smt__TLA____Mem smt__VARIABLE__vote__
                (smt__TLA____FunSet smt__CONSTANT__Node__
                  (smt__TLA____Cup smt__CONSTANT__Value__
                    (smt__TLA____SetEnum__1 smt__CONSTANT__Nil__))))
              (smt__TLA____Mem smt__VARIABLE__voted__
                (smt__TLA____FunSet smt__CONSTANT__Node__ smt__TLA____BoolSet))
              (smt__TLA____Mem smt__VARIABLE__decided__
                (smt__TLA____Subset smt__CONSTANT__Value__)))
            (forall ((smt__CONSTANT__vi__ Idv) (smt__CONSTANT__vj__ Idv))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__vi__
                    smt__VARIABLE__decided__)
                  (smt__TLA____Mem smt__CONSTANT__vj__
                    smt__VARIABLE__decided__))
                (= smt__CONSTANT__vi__ smt__CONSTANT__vj__)))
            (forall ((smt__CONSTANT__s__ Idv) (smt__CONSTANT__t__ Idv))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__s__ smt__CONSTANT__Node__)
                  (smt__TLA____Mem smt__CONSTANT__t__ smt__CONSTANT__Node__))
                (forall ((smt__CONSTANT__Q__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__Q__
                      (smt__TLA____SetSt__flatnd__1
                        (smt__TLA____Subset smt__CONSTANT__Node__)))
                    (forall ((smt__CONSTANT__v__ Idv))
                      (=>
                        (smt__TLA____Mem smt__CONSTANT__v__
                          smt__CONSTANT__Value__)
                        (exists ((smt__CONSTANT__n__ Idv))
                          (and
                            (smt__TLA____Mem smt__CONSTANT__n__
                              smt__CONSTANT__Q__)
                            (or
                              (=
                                (smt__TLA____FunApp smt__VARIABLE__voted__
                                  smt__CONSTANT__s__) smt__TLA____Tt__Idv)
                              (not
                                (=
                                  (smt__TLA____FunApp smt__VARIABLE__vote__
                                    smt__CONSTANT__s__) smt__CONSTANT__v__)))))))))))
            (forall ((smt__CONSTANT__s__ Idv) (smt__CONSTANT__t__ Idv))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__s__ smt__CONSTANT__Node__)
                  (smt__TLA____Mem smt__CONSTANT__t__ smt__CONSTANT__Node__))
                (forall ((smt__CONSTANT__Q__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__Q__
                      (smt__TLA____SetSt__flatnd__1
                        (smt__TLA____Subset smt__CONSTANT__Node__)))
                    (forall ((smt__CONSTANT__v__ Idv))
                      (=>
                        (smt__TLA____Mem smt__CONSTANT__v__
                          smt__CONSTANT__Value__)
                        (exists ((smt__CONSTANT__n__ Idv))
                          (and
                            (smt__TLA____Mem smt__CONSTANT__n__
                              smt__CONSTANT__Q__)
                            (or
                              (=
                                (smt__TLA____FunApp smt__VARIABLE__vote__
                                  smt__CONSTANT__n__) smt__CONSTANT__v__)
                              (not
                                (smt__TLA____Mem smt__CONSTANT__v__
                                  smt__VARIABLE__decided__))))))))))))
          (or
            (exists ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__v__ Idv))
              (and (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__v__ smt__CONSTANT__Value__)
                (and
                  (not
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__voted__
                        smt__CONSTANT__i__) smt__TLA____Tt__Idv))
                  (= smt__VARIABLE__vote____prime
                    (smt__TLA____FunExcept smt__VARIABLE__vote__
                      smt__CONSTANT__i__ smt__CONSTANT__v__))
                  (= smt__VARIABLE__voted____prime
                    (smt__TLA____FunExcept smt__VARIABLE__voted__
                      smt__CONSTANT__i__ (smt__TLA____Cast__Bool true)))
                  (= smt__VARIABLE__decided____prime smt__VARIABLE__decided__))))
            (exists ((smt__CONSTANT__v__ Idv) (smt__CONSTANT__Q__ Idv))
              (and
                (smt__TLA____Mem smt__CONSTANT__v__ smt__CONSTANT__Value__)
                (smt__TLA____Mem smt__CONSTANT__Q__
                  (smt__TLA____SetSt__flatnd__1
                    (smt__TLA____Subset smt__CONSTANT__Node__)))
                (and
                  (forall ((smt__CONSTANT__n__ Idv))
                    (=>
                      (smt__TLA____Mem smt__CONSTANT__n__ smt__CONSTANT__Q__)
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__vote__
                          smt__CONSTANT__n__) smt__CONSTANT__v__)))
                  (= smt__VARIABLE__decided____prime
                    (smt__TLA____Cup smt__VARIABLE__decided__
                      (smt__TLA____SetEnum__1 smt__CONSTANT__v__)))
                  (and (= smt__VARIABLE__vote____prime smt__VARIABLE__vote__)
                    (= smt__VARIABLE__voted____prime smt__VARIABLE__voted__)))))))
        (and
          (and
            (smt__TLA____Mem smt__VARIABLE__vote____prime
              (smt__TLA____FunSet smt__CONSTANT__Node__
                (smt__TLA____Cup smt__CONSTANT__Value__
                  (smt__TLA____SetEnum__1 smt__CONSTANT__Nil__))))
            (smt__TLA____Mem smt__VARIABLE__voted____prime
              (smt__TLA____FunSet smt__CONSTANT__Node__ smt__TLA____BoolSet))
            (smt__TLA____Mem smt__VARIABLE__decided____prime
              (smt__TLA____Subset smt__CONSTANT__Value__)))
          (forall ((smt__CONSTANT__vi__ Idv) (smt__CONSTANT__vj__ Idv))
            (=>
              (and
                (smt__TLA____Mem smt__CONSTANT__vi__
                  smt__VARIABLE__decided____prime)
                (smt__TLA____Mem smt__CONSTANT__vj__
                  smt__VARIABLE__decided____prime))
              (= smt__CONSTANT__vi__ smt__CONSTANT__vj__)))
          (forall ((smt__CONSTANT__s__ Idv) (smt__CONSTANT__t__ Idv))
            (=>
              (and (smt__TLA____Mem smt__CONSTANT__s__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__t__ smt__CONSTANT__Node__))
              (forall ((smt__CONSTANT__Q__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__Q__
                    (smt__TLA____SetSt__flatnd__1
                      (smt__TLA____Subset smt__CONSTANT__Node__)))
                  (forall ((smt__CONSTANT__v__ Idv))
                    (=>
                      (smt__TLA____Mem smt__CONSTANT__v__
                        smt__CONSTANT__Value__)
                      (exists ((smt__CONSTANT__n__ Idv))
                        (and
                          (smt__TLA____Mem smt__CONSTANT__n__
                            smt__CONSTANT__Q__)
                          (or
                            (=
                              (smt__TLA____FunApp
                                smt__VARIABLE__voted____prime
                                smt__CONSTANT__s__) smt__TLA____Tt__Idv)
                            (not
                              (=
                                (smt__TLA____FunApp
                                  smt__VARIABLE__vote____prime
                                  smt__CONSTANT__s__) smt__CONSTANT__v__)))))))))))
          (forall ((smt__CONSTANT__s__ Idv) (smt__CONSTANT__t__ Idv))
            (=>
              (and (smt__TLA____Mem smt__CONSTANT__s__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__t__ smt__CONSTANT__Node__))
              (forall ((smt__CONSTANT__Q__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__Q__
                    (smt__TLA____SetSt__flatnd__1
                      (smt__TLA____Subset smt__CONSTANT__Node__)))
                  (forall ((smt__CONSTANT__v__ Idv))
                    (=>
                      (smt__TLA____Mem smt__CONSTANT__v__
                        smt__CONSTANT__Value__)
                      (exists ((smt__CONSTANT__n__ Idv))
                        (and
                          (smt__TLA____Mem smt__CONSTANT__n__
                            smt__CONSTANT__Q__)
                          (or
                            (=
                              (smt__TLA____FunApp
                                smt__VARIABLE__vote____prime
                                smt__CONSTANT__n__) smt__CONSTANT__v__)
                            (not
                              (smt__TLA____Mem smt__CONSTANT__v__
                                smt__VARIABLE__decided____prime))))))))))))))
    :named |Goal|))

(check-sat)
(exit)
