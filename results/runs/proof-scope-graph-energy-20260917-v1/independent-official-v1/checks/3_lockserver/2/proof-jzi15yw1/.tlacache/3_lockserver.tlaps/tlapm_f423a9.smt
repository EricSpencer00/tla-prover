;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Server_,
;;	       NEW CONSTANT CONSTANT_Client_,
;;	       NEW CONSTANT CONSTANT_Nil_,
;;	       NEW VARIABLE VARIABLE_semaphore_,
;;	       NEW VARIABLE VARIABLE_clientlocks_
;;	PROVE  (/\ /\ VARIABLE_semaphore_ \in [CONSTANT_Server_ -> BOOLEAN]
;;	           /\ VARIABLE_clientlocks_
;;	              \in [CONSTANT_Client_ -> SUBSET CONSTANT_Server_]
;;	        /\ \A CONSTANT_ci_, CONSTANT_cj_ \in CONSTANT_Client_ :
;;	              VARIABLE_clientlocks_[CONSTANT_ci_]
;;	              \cap VARIABLE_clientlocks_[CONSTANT_cj_] # {}
;;	              => CONSTANT_ci_ = CONSTANT_cj_
;;	        /\ \A CONSTANT_VARS_ \in CONSTANT_Server_ :
;;	              \A CONSTANT_VARC_ \in CONSTANT_Client_ :
;;	                 ~CONSTANT_VARS_ \in VARIABLE_clientlocks_[CONSTANT_VARC_]
;;	                 \/ ~VARIABLE_semaphore_[CONSTANT_VARS_])
;;	       /\ (\/ \E CONSTANT_c_ \in CONSTANT_Client_,
;;	                 CONSTANT_s_ \in CONSTANT_Server_ :
;;	                 /\ VARIABLE_semaphore_[CONSTANT_s_] = TRUE
;;	                 /\ ?VARIABLE_clientlocks_#prime
;;	                    = [VARIABLE_clientlocks_ EXCEPT
;;	                         ![CONSTANT_c_] = VARIABLE_clientlocks_[CONSTANT_c_]
;;	                                          \cup {CONSTANT_s_}]
;;	                 /\ ?VARIABLE_semaphore_#prime
;;	                    = [VARIABLE_semaphore_ EXCEPT ![CONSTANT_s_] = FALSE]
;;	           \/ \E CONSTANT_c_ \in CONSTANT_Client_,
;;	                 CONSTANT_s_ \in CONSTANT_Server_ :
;;	                 /\ CONSTANT_s_ \in VARIABLE_clientlocks_[CONSTANT_c_]
;;	                 /\ ?VARIABLE_clientlocks_#prime
;;	                    = [VARIABLE_clientlocks_ EXCEPT
;;	                         ![CONSTANT_c_] = VARIABLE_clientlocks_[CONSTANT_c_]
;;	                                          \ {CONSTANT_s_}]
;;	                 /\ ?VARIABLE_semaphore_#prime
;;	                    = [VARIABLE_semaphore_ EXCEPT ![CONSTANT_s_] = TRUE])
;;	       => (/\ /\ ?VARIABLE_semaphore_#prime \in [CONSTANT_Server_ -> BOOLEAN]
;;	              /\ ?VARIABLE_clientlocks_#prime
;;	                 \in [CONSTANT_Client_ -> SUBSET CONSTANT_Server_]
;;	           /\ \A CONSTANT_ci_, CONSTANT_cj_ \in CONSTANT_Client_ :
;;	                 ?VARIABLE_clientlocks_#prime[CONSTANT_ci_]
;;	                 \cap ?VARIABLE_clientlocks_#prime[CONSTANT_cj_] # {}
;;	                 => CONSTANT_ci_ = CONSTANT_cj_
;;	           /\ \A CONSTANT_VARS_ \in CONSTANT_Server_ :
;;	                 \A CONSTANT_VARC_ \in CONSTANT_Client_ :
;;	                    ~CONSTANT_VARS_
;;	                     \in ?VARIABLE_clientlocks_#prime[CONSTANT_VARC_]
;;	                    \/ ~?VARIABLE_semaphore_#prime[CONSTANT_VARS_])
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./3_lockserver.tla", line 75, characters 53-54

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____BoolSet () Idv)

(declare-fun smt__TLA____Cap (Idv Idv) Idv)

(declare-fun smt__TLA____Cast__Bool (Bool) Idv)

(declare-fun smt__TLA____Cup (Idv Idv) Idv)

(declare-fun smt__TLA____FunApp (Idv Idv) Idv)

(declare-fun smt__TLA____FunDom (Idv) Idv)

(declare-fun smt__TLA____FunExcept (Idv Idv Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA____FunIsafcn (Idv) Bool)

(declare-fun smt__TLA____FunSet (Idv Idv) Idv)

(declare-fun smt__TLA____Mem (Idv Idv) Bool)

(declare-fun smt__TLA____SetEnum__0 () Idv)

(declare-fun smt__TLA____SetEnum__1 (Idv) Idv)

(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLA____SetMinus (Idv Idv) Idv)

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

;; Axiom: CapDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (= (smt__TLA____Mem smt__x (smt__TLA____Cap smt__a smt__b))
          (and (smt__TLA____Mem smt__x smt__a)
            (smt__TLA____Mem smt__x smt__b)))
        :pattern ((smt__TLA____Mem smt__x (smt__TLA____Cap smt__a smt__b)))
        :pattern ((smt__TLA____Mem smt__x smt__a)
                   (smt__TLA____Cap smt__a smt__b))
        :pattern ((smt__TLA____Mem smt__x smt__b)
                   (smt__TLA____Cap smt__a smt__b)))) :named |CapDef|))

;; Axiom: SetMinusDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (= (smt__TLA____Mem smt__x (smt__TLA____SetMinus smt__a smt__b))
          (and (smt__TLA____Mem smt__x smt__a)
            (not (smt__TLA____Mem smt__x smt__b))))
        :pattern ((smt__TLA____Mem smt__x
                    (smt__TLA____SetMinus smt__a smt__b)))
        :pattern ((smt__TLA____Mem smt__x smt__a)
                   (smt__TLA____SetMinus smt__a smt__b))
        :pattern ((smt__TLA____Mem smt__x smt__b)
                   (smt__TLA____SetMinus smt__a smt__b))))
    :named |SetMinusDef|))

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

;; Axiom: DisjointTrigger
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (smt__TLA____SetExtTrigger (smt__TLA____Cap smt__x smt__y)
          smt__TLA____SetEnum__0) :pattern ((smt__TLA____Cap smt__x smt__y))))
    :named |DisjointTrigger|))

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

;; Axiom: TypeGuardIntro Bool
(assert
  (!
    (forall ((smt__z Bool))
      (!
        (smt__TLA____Mem (smt__TLA____Cast__Bool smt__z) smt__TLA____BoolSet)
        :pattern ((smt__TLA____Cast__Bool smt__z))))
    :named |TypeGuardIntro Bool|))

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

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_EnabledWrapper_' (second-order)

; omitted declaration of 'CONSTANT_CdotWrapper_' (second-order)

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

(declare-fun smt__CONSTANT__Server__ () Idv)

(declare-fun smt__CONSTANT__Client__ () Idv)

(declare-fun smt__CONSTANT__Nil__ () Idv)

(declare-fun smt__VARIABLE__semaphore__ () Idv)

(declare-fun smt__VARIABLE__semaphore____prime () Idv)

(declare-fun smt__VARIABLE__clientlocks__ () Idv)

(declare-fun smt__VARIABLE__clientlocks____prime () Idv)

;; Goal
(assert
  (!
    (not
      (=>
        (and
          (and
            (and
              (smt__TLA____Mem smt__VARIABLE__semaphore__
                (smt__TLA____FunSet smt__CONSTANT__Server__
                  smt__TLA____BoolSet))
              (smt__TLA____Mem smt__VARIABLE__clientlocks__
                (smt__TLA____FunSet smt__CONSTANT__Client__
                  (smt__TLA____Subset smt__CONSTANT__Server__))))
            (forall ((smt__CONSTANT__ci__ Idv) (smt__CONSTANT__cj__ Idv))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__ci__
                    smt__CONSTANT__Client__)
                  (smt__TLA____Mem smt__CONSTANT__cj__
                    smt__CONSTANT__Client__))
                (=>
                  (distinct
                    (smt__TLA____Cap
                      (smt__TLA____FunApp smt__VARIABLE__clientlocks__
                        smt__CONSTANT__ci__)
                      (smt__TLA____FunApp smt__VARIABLE__clientlocks__
                        smt__CONSTANT__cj__)) smt__TLA____SetEnum__0)
                  (= smt__CONSTANT__ci__ smt__CONSTANT__cj__))))
            (forall ((smt__CONSTANT__VARS__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARS__
                  smt__CONSTANT__Server__)
                (forall ((smt__CONSTANT__VARC__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__VARC__
                      smt__CONSTANT__Client__)
                    (or
                      (not
                        (smt__TLA____Mem smt__CONSTANT__VARS__
                          (smt__TLA____FunApp smt__VARIABLE__clientlocks__
                            smt__CONSTANT__VARC__)))
                      (not
                        (=
                          (smt__TLA____FunApp smt__VARIABLE__semaphore__
                            smt__CONSTANT__VARS__) smt__TLA____Tt__Idv))))))))
          (or
            (exists ((smt__CONSTANT__c__ Idv) (smt__CONSTANT__s__ Idv))
              (and
                (smt__TLA____Mem smt__CONSTANT__c__ smt__CONSTANT__Client__)
                (smt__TLA____Mem smt__CONSTANT__s__ smt__CONSTANT__Server__)
                (and
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__semaphore__
                      smt__CONSTANT__s__) (smt__TLA____Cast__Bool true))
                  (= smt__VARIABLE__clientlocks____prime
                    (smt__TLA____FunExcept smt__VARIABLE__clientlocks__
                      smt__CONSTANT__c__
                      (smt__TLA____Cup
                        (smt__TLA____FunApp smt__VARIABLE__clientlocks__
                          smt__CONSTANT__c__)
                        (smt__TLA____SetEnum__1 smt__CONSTANT__s__))))
                  (= smt__VARIABLE__semaphore____prime
                    (smt__TLA____FunExcept smt__VARIABLE__semaphore__
                      smt__CONSTANT__s__ (smt__TLA____Cast__Bool false))))))
            (exists ((smt__CONSTANT__c__ Idv) (smt__CONSTANT__s__ Idv))
              (and
                (smt__TLA____Mem smt__CONSTANT__c__ smt__CONSTANT__Client__)
                (smt__TLA____Mem smt__CONSTANT__s__ smt__CONSTANT__Server__)
                (and
                  (smt__TLA____Mem smt__CONSTANT__s__
                    (smt__TLA____FunApp smt__VARIABLE__clientlocks__
                      smt__CONSTANT__c__))
                  (= smt__VARIABLE__clientlocks____prime
                    (smt__TLA____FunExcept smt__VARIABLE__clientlocks__
                      smt__CONSTANT__c__
                      (smt__TLA____SetMinus
                        (smt__TLA____FunApp smt__VARIABLE__clientlocks__
                          smt__CONSTANT__c__)
                        (smt__TLA____SetEnum__1 smt__CONSTANT__s__))))
                  (= smt__VARIABLE__semaphore____prime
                    (smt__TLA____FunExcept smt__VARIABLE__semaphore__
                      smt__CONSTANT__s__ (smt__TLA____Cast__Bool true))))))))
        (and
          (and
            (smt__TLA____Mem smt__VARIABLE__semaphore____prime
              (smt__TLA____FunSet smt__CONSTANT__Server__ smt__TLA____BoolSet))
            (smt__TLA____Mem smt__VARIABLE__clientlocks____prime
              (smt__TLA____FunSet smt__CONSTANT__Client__
                (smt__TLA____Subset smt__CONSTANT__Server__))))
          (forall ((smt__CONSTANT__ci__ Idv) (smt__CONSTANT__cj__ Idv))
            (=>
              (and
                (smt__TLA____Mem smt__CONSTANT__ci__ smt__CONSTANT__Client__)
                (smt__TLA____Mem smt__CONSTANT__cj__ smt__CONSTANT__Client__))
              (=>
                (not
                  (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__
                    (smt__TLA____Cap
                      (smt__TLA____FunApp smt__VARIABLE__clientlocks____prime
                        smt__CONSTANT__ci__)
                      (smt__TLA____FunApp smt__VARIABLE__clientlocks____prime
                        smt__CONSTANT__cj__)) smt__TLA____SetEnum__0))
                (= smt__CONSTANT__ci__ smt__CONSTANT__cj__))))
          (forall ((smt__CONSTANT__VARS__ Idv))
            (=>
              (smt__TLA____Mem smt__CONSTANT__VARS__ smt__CONSTANT__Server__)
              (forall ((smt__CONSTANT__VARC__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__VARC__
                    smt__CONSTANT__Client__)
                  (or
                    (not
                      (smt__TLA____Mem smt__CONSTANT__VARS__
                        (smt__TLA____FunApp
                          smt__VARIABLE__clientlocks____prime
                          smt__CONSTANT__VARC__)))
                    (not
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__semaphore____prime
                          smt__CONSTANT__VARS__) smt__TLA____Tt__Idv))))))))))
    :named |Goal|))

(check-sat)
(exit)
