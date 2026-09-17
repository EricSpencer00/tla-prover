;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Node_,
;;	       NEW VARIABLE VARIABLE_internal_,
;;	       NEW VARIABLE VARIABLE_sent_,
;;	       NEW VARIABLE VARIABLE_allowed_in_
;;	PROVE  (/\ /\ VARIABLE_internal_ \in [CONSTANT_Node_ -> BOOLEAN]
;;	           /\ VARIABLE_sent_ \in [CONSTANT_Node_ -> SUBSET CONSTANT_Node_]
;;	           /\ VARIABLE_allowed_in_ \in SUBSET CONSTANT_Node_
;;	        /\ \A CONSTANT_s_, CONSTANT_d_ \in CONSTANT_Node_ :
;;	              CONSTANT_d_ \in VARIABLE_sent_[CONSTANT_s_]
;;	              /\ VARIABLE_internal_[CONSTANT_d_]
;;	              => (\E CONSTANT_i_ \in CONSTANT_Node_ :
;;	                     VARIABLE_internal_[CONSTANT_i_]
;;	                     /\ CONSTANT_s_ \in VARIABLE_sent_[CONSTANT_i_])
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                 \E CONSTANT_VARK_ \in CONSTANT_Node_ :
;;	                    VARIABLE_internal_[CONSTANT_VARI_]
;;	                    \/ ~CONSTANT_VARJ_ \in VARIABLE_sent_[CONSTANT_VARJ_]
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                 \E CONSTANT_VARK_ \in CONSTANT_Node_ :
;;	                    CONSTANT_VARJ_ \in VARIABLE_sent_[CONSTANT_VARK_]
;;	                    \/ ~CONSTANT_VARJ_ \in VARIABLE_allowed_in_
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                 \E CONSTANT_VARK_ \in CONSTANT_Node_ :
;;	                    ~CONSTANT_VARI_ \in VARIABLE_allowed_in_
;;	                    \/ ~VARIABLE_internal_[CONSTANT_VARI_]
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                 \E CONSTANT_VARK_ \in CONSTANT_Node_ :
;;	                    VARIABLE_internal_[CONSTANT_VARI_]
;;	                    \/ VARIABLE_internal_[CONSTANT_VARJ_]
;;	                    \/ ~CONSTANT_VARI_ \in VARIABLE_sent_[CONSTANT_VARJ_])
;;	       /\ (\/ \E CONSTANT_s_, CONSTANT_t_ \in CONSTANT_Node_ :
;;	                 /\ VARIABLE_internal_[CONSTANT_s_]
;;	                 /\ ~VARIABLE_internal_[CONSTANT_t_]
;;	                 /\ ?VARIABLE_sent_#prime
;;	                    = [VARIABLE_sent_ EXCEPT
;;	                         ![CONSTANT_s_] = VARIABLE_sent_[CONSTANT_s_]
;;	                                          \cup {CONSTANT_t_}]
;;	                 /\ ?VARIABLE_allowed_in_#prime
;;	                    = VARIABLE_allowed_in_ \cup {CONSTANT_t_}
;;	                 /\ ?VARIABLE_internal_#prime = VARIABLE_internal_
;;	           \/ \E CONSTANT_s_, CONSTANT_t_ \in CONSTANT_Node_ :
;;	                 /\ ~VARIABLE_internal_[CONSTANT_s_]
;;	                 /\ VARIABLE_internal_[CONSTANT_t_]
;;	                 /\ CONSTANT_s_ \in VARIABLE_allowed_in_
;;	                 /\ ?VARIABLE_sent_#prime
;;	                    = [VARIABLE_sent_ EXCEPT
;;	                         ![CONSTANT_s_] = VARIABLE_sent_[CONSTANT_s_]
;;	                                          \cup {CONSTANT_t_}]
;;	                 /\ /\ ?VARIABLE_internal_#prime = VARIABLE_internal_
;;	                    /\ ?VARIABLE_allowed_in_#prime = VARIABLE_allowed_in_)
;;	       => (/\ /\ ?VARIABLE_internal_#prime \in [CONSTANT_Node_ -> BOOLEAN]
;;	              /\ ?VARIABLE_sent_#prime
;;	                 \in [CONSTANT_Node_ -> SUBSET CONSTANT_Node_]
;;	              /\ ?VARIABLE_allowed_in_#prime \in SUBSET CONSTANT_Node_
;;	           /\ \A CONSTANT_s_, CONSTANT_d_ \in CONSTANT_Node_ :
;;	                 CONSTANT_d_ \in ?VARIABLE_sent_#prime[CONSTANT_s_]
;;	                 /\ ?VARIABLE_internal_#prime[CONSTANT_d_]
;;	                 => (\E CONSTANT_i_ \in CONSTANT_Node_ :
;;	                        ?VARIABLE_internal_#prime[CONSTANT_i_]
;;	                        /\ CONSTANT_s_ \in ?VARIABLE_sent_#prime[CONSTANT_i_])
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                    \E CONSTANT_VARK_ \in CONSTANT_Node_ :
;;	                       ?VARIABLE_internal_#prime[CONSTANT_VARI_]
;;	                       \/ ~CONSTANT_VARJ_
;;	                           \in ?VARIABLE_sent_#prime[CONSTANT_VARJ_]
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                    \E CONSTANT_VARK_ \in CONSTANT_Node_ :
;;	                       CONSTANT_VARJ_
;;	                       \in ?VARIABLE_sent_#prime[CONSTANT_VARK_]
;;	                       \/ ~CONSTANT_VARJ_ \in ?VARIABLE_allowed_in_#prime
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                    \E CONSTANT_VARK_ \in CONSTANT_Node_ :
;;	                       ~CONSTANT_VARI_ \in ?VARIABLE_allowed_in_#prime
;;	                       \/ ~?VARIABLE_internal_#prime[CONSTANT_VARI_]
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                    \E CONSTANT_VARK_ \in CONSTANT_Node_ :
;;	                       ?VARIABLE_internal_#prime[CONSTANT_VARI_]
;;	                       \/ ?VARIABLE_internal_#prime[CONSTANT_VARJ_]
;;	                       \/ ~CONSTANT_VARI_
;;	                           \in ?VARIABLE_sent_#prime[CONSTANT_VARJ_])
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./27_firewall.tla", line 69, characters 53-54

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____BoolSet () Idv)

(declare-fun smt__TLA____Cup (Idv Idv) Idv)

(declare-fun smt__TLA____FunApp (Idv Idv) Idv)

(declare-fun smt__TLA____FunDom (Idv) Idv)

(declare-fun smt__TLA____FunExcept (Idv Idv Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA____FunIsafcn (Idv) Bool)

(declare-fun smt__TLA____FunSet (Idv Idv) Idv)

(declare-fun smt__TLA____Mem (Idv Idv) Bool)

(declare-fun smt__TLA____SetEnum__1 (Idv) Idv)

(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)

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

;; Axiom: EnumDefIntro 1
(assert
  (!
    (forall ((smt__a1 Idv))
      (! (smt__TLA____Mem smt__a1 (smt__TLA____SetEnum__1 smt__a1))
        :pattern ((smt__TLA____SetEnum__1 smt__a1)))) :named |EnumDefIntro 1|))

;; Axiom: EnumDefElim 1
(assert
  (!
    (forall ((smt__a1 Idv) (smt__x Idv))
      (!
        (=> (smt__TLA____Mem smt__x (smt__TLA____SetEnum__1 smt__a1))
          (= smt__x smt__a1))
        :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetEnum__1 smt__a1)))))
    :named |EnumDefElim 1|))

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

(declare-fun smt__CONSTANT__Node__ () Idv)

(declare-fun smt__VARIABLE__internal__ () Idv)

(declare-fun smt__VARIABLE__internal____prime () Idv)

(declare-fun smt__VARIABLE__sent__ () Idv)

(declare-fun smt__VARIABLE__sent____prime () Idv)

(declare-fun smt__VARIABLE__allowed__in__ () Idv)

(declare-fun smt__VARIABLE__allowed__in____prime () Idv)

; hidden fact

; hidden fact

;; Goal
(assert
  (!
    (not
      (=>
        (and
          (and
            (and
              (smt__TLA____Mem smt__VARIABLE__internal__
                (smt__TLA____FunSet smt__CONSTANT__Node__ smt__TLA____BoolSet))
              (smt__TLA____Mem smt__VARIABLE__sent__
                (smt__TLA____FunSet smt__CONSTANT__Node__
                  (smt__TLA____Subset smt__CONSTANT__Node__)))
              (smt__TLA____Mem smt__VARIABLE__allowed__in__
                (smt__TLA____Subset smt__CONSTANT__Node__)))
            (forall ((smt__CONSTANT__s__ Idv) (smt__CONSTANT__d__ Idv))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__s__ smt__CONSTANT__Node__)
                  (smt__TLA____Mem smt__CONSTANT__d__ smt__CONSTANT__Node__))
                (=>
                  (and
                    (smt__TLA____Mem smt__CONSTANT__d__
                      (smt__TLA____FunApp smt__VARIABLE__sent__
                        smt__CONSTANT__s__))
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__internal__
                        smt__CONSTANT__d__) smt__TLA____Tt__Idv))
                  (exists ((smt__CONSTANT__i__ Idv))
                    (and
                      (smt__TLA____Mem smt__CONSTANT__i__
                        smt__CONSTANT__Node__)
                      (and
                        (=
                          (smt__TLA____FunApp smt__VARIABLE__internal__
                            smt__CONSTANT__i__) smt__TLA____Tt__Idv)
                        (smt__TLA____Mem smt__CONSTANT__s__
                          (smt__TLA____FunApp smt__VARIABLE__sent__
                            smt__CONSTANT__i__))))))))
            (forall ((smt__CONSTANT__VARI__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__VARJ__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__VARJ__
                      smt__CONSTANT__Node__)
                    (exists ((smt__CONSTANT__VARK__ Idv))
                      (and
                        (smt__TLA____Mem smt__CONSTANT__VARK__
                          smt__CONSTANT__Node__)
                        (or
                          (=
                            (smt__TLA____FunApp smt__VARIABLE__internal__
                              smt__CONSTANT__VARI__) smt__TLA____Tt__Idv)
                          (not
                            (smt__TLA____Mem smt__CONSTANT__VARJ__
                              (smt__TLA____FunApp smt__VARIABLE__sent__
                                smt__CONSTANT__VARJ__))))))))))
            (forall ((smt__CONSTANT__VARI__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__VARJ__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__VARJ__
                      smt__CONSTANT__Node__)
                    (exists ((smt__CONSTANT__VARK__ Idv))
                      (and
                        (smt__TLA____Mem smt__CONSTANT__VARK__
                          smt__CONSTANT__Node__)
                        (or
                          (smt__TLA____Mem smt__CONSTANT__VARJ__
                            (smt__TLA____FunApp smt__VARIABLE__sent__
                              smt__CONSTANT__VARK__))
                          (not
                            (smt__TLA____Mem smt__CONSTANT__VARJ__
                              smt__VARIABLE__allowed__in__)))))))))
            (forall ((smt__CONSTANT__VARI__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__VARJ__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__VARJ__
                      smt__CONSTANT__Node__)
                    (exists ((smt__CONSTANT__VARK__ Idv))
                      (and
                        (smt__TLA____Mem smt__CONSTANT__VARK__
                          smt__CONSTANT__Node__)
                        (or
                          (not
                            (smt__TLA____Mem smt__CONSTANT__VARI__
                              smt__VARIABLE__allowed__in__))
                          (not
                            (=
                              (smt__TLA____FunApp smt__VARIABLE__internal__
                                smt__CONSTANT__VARI__) smt__TLA____Tt__Idv)))))))))
            (forall ((smt__CONSTANT__VARI__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__VARJ__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__VARJ__
                      smt__CONSTANT__Node__)
                    (exists ((smt__CONSTANT__VARK__ Idv))
                      (and
                        (smt__TLA____Mem smt__CONSTANT__VARK__
                          smt__CONSTANT__Node__)
                        (or
                          (or
                            (=
                              (smt__TLA____FunApp smt__VARIABLE__internal__
                                smt__CONSTANT__VARI__) smt__TLA____Tt__Idv)
                            (=
                              (smt__TLA____FunApp smt__VARIABLE__internal__
                                smt__CONSTANT__VARJ__) smt__TLA____Tt__Idv))
                          (not
                            (smt__TLA____Mem smt__CONSTANT__VARI__
                              (smt__TLA____FunApp smt__VARIABLE__sent__
                                smt__CONSTANT__VARJ__)))))))))))
          (or
            (exists ((smt__CONSTANT__s__ Idv) (smt__CONSTANT__t__ Idv))
              (and (smt__TLA____Mem smt__CONSTANT__s__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__t__ smt__CONSTANT__Node__)
                (and
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__internal__
                      smt__CONSTANT__s__) smt__TLA____Tt__Idv)
                  (not
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__internal__
                        smt__CONSTANT__t__) smt__TLA____Tt__Idv))
                  (= smt__VARIABLE__sent____prime
                    (smt__TLA____FunExcept smt__VARIABLE__sent__
                      smt__CONSTANT__s__
                      (smt__TLA____Cup
                        (smt__TLA____FunApp smt__VARIABLE__sent__
                          smt__CONSTANT__s__)
                        (smt__TLA____SetEnum__1 smt__CONSTANT__t__))))
                  (= smt__VARIABLE__allowed__in____prime
                    (smt__TLA____Cup smt__VARIABLE__allowed__in__
                      (smt__TLA____SetEnum__1 smt__CONSTANT__t__)))
                  (= smt__VARIABLE__internal____prime
                    smt__VARIABLE__internal__))))
            (exists ((smt__CONSTANT__s__ Idv) (smt__CONSTANT__t__ Idv))
              (and (smt__TLA____Mem smt__CONSTANT__s__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__t__ smt__CONSTANT__Node__)
                (and
                  (not
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__internal__
                        smt__CONSTANT__s__) smt__TLA____Tt__Idv))
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__internal__
                      smt__CONSTANT__t__) smt__TLA____Tt__Idv)
                  (smt__TLA____Mem smt__CONSTANT__s__
                    smt__VARIABLE__allowed__in__)
                  (= smt__VARIABLE__sent____prime
                    (smt__TLA____FunExcept smt__VARIABLE__sent__
                      smt__CONSTANT__s__
                      (smt__TLA____Cup
                        (smt__TLA____FunApp smt__VARIABLE__sent__
                          smt__CONSTANT__s__)
                        (smt__TLA____SetEnum__1 smt__CONSTANT__t__))))
                  (and
                    (= smt__VARIABLE__internal____prime
                      smt__VARIABLE__internal__)
                    (= smt__VARIABLE__allowed__in____prime
                      smt__VARIABLE__allowed__in__)))))))
        (and
          (and
            (smt__TLA____Mem smt__VARIABLE__internal____prime
              (smt__TLA____FunSet smt__CONSTANT__Node__ smt__TLA____BoolSet))
            (smt__TLA____Mem smt__VARIABLE__sent____prime
              (smt__TLA____FunSet smt__CONSTANT__Node__
                (smt__TLA____Subset smt__CONSTANT__Node__)))
            (smt__TLA____Mem smt__VARIABLE__allowed__in____prime
              (smt__TLA____Subset smt__CONSTANT__Node__)))
          (forall ((smt__CONSTANT__s__ Idv) (smt__CONSTANT__d__ Idv))
            (=>
              (and (smt__TLA____Mem smt__CONSTANT__s__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__d__ smt__CONSTANT__Node__))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__d__
                    (smt__TLA____FunApp smt__VARIABLE__sent____prime
                      smt__CONSTANT__s__))
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__internal____prime
                      smt__CONSTANT__d__) smt__TLA____Tt__Idv))
                (exists ((smt__CONSTANT__i__ Idv))
                  (and
                    (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Node__)
                    (and
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__internal____prime
                          smt__CONSTANT__i__) smt__TLA____Tt__Idv)
                      (smt__TLA____Mem smt__CONSTANT__s__
                        (smt__TLA____FunApp smt__VARIABLE__sent____prime
                          smt__CONSTANT__i__))))))))
          (forall ((smt__CONSTANT__VARI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__VARJ__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__VARJ__
                    smt__CONSTANT__Node__)
                  (exists ((smt__CONSTANT__VARK__ Idv))
                    (and
                      (smt__TLA____Mem smt__CONSTANT__VARK__
                        smt__CONSTANT__Node__)
                      (or
                        (=
                          (smt__TLA____FunApp
                            smt__VARIABLE__internal____prime
                            smt__CONSTANT__VARI__) smt__TLA____Tt__Idv)
                        (not
                          (smt__TLA____Mem smt__CONSTANT__VARJ__
                            (smt__TLA____FunApp smt__VARIABLE__sent____prime
                              smt__CONSTANT__VARJ__))))))))))
          (forall ((smt__CONSTANT__VARI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__VARJ__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__VARJ__
                    smt__CONSTANT__Node__)
                  (exists ((smt__CONSTANT__VARK__ Idv))
                    (and
                      (smt__TLA____Mem smt__CONSTANT__VARK__
                        smt__CONSTANT__Node__)
                      (or
                        (smt__TLA____Mem smt__CONSTANT__VARJ__
                          (smt__TLA____FunApp smt__VARIABLE__sent____prime
                            smt__CONSTANT__VARK__))
                        (not
                          (smt__TLA____Mem smt__CONSTANT__VARJ__
                            smt__VARIABLE__allowed__in____prime)))))))))
          (forall ((smt__CONSTANT__VARI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__VARJ__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__VARJ__
                    smt__CONSTANT__Node__)
                  (exists ((smt__CONSTANT__VARK__ Idv))
                    (and
                      (smt__TLA____Mem smt__CONSTANT__VARK__
                        smt__CONSTANT__Node__)
                      (or
                        (not
                          (smt__TLA____Mem smt__CONSTANT__VARI__
                            smt__VARIABLE__allowed__in____prime))
                        (not
                          (=
                            (smt__TLA____FunApp
                              smt__VARIABLE__internal____prime
                              smt__CONSTANT__VARI__) smt__TLA____Tt__Idv)))))))))
          (forall ((smt__CONSTANT__VARI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__VARJ__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__VARJ__
                    smt__CONSTANT__Node__)
                  (exists ((smt__CONSTANT__VARK__ Idv))
                    (and
                      (smt__TLA____Mem smt__CONSTANT__VARK__
                        smt__CONSTANT__Node__)
                      (or
                        (or
                          (=
                            (smt__TLA____FunApp
                              smt__VARIABLE__internal____prime
                              smt__CONSTANT__VARI__) smt__TLA____Tt__Idv)
                          (=
                            (smt__TLA____FunApp
                              smt__VARIABLE__internal____prime
                              smt__CONSTANT__VARJ__) smt__TLA____Tt__Idv))
                        (not
                          (smt__TLA____Mem smt__CONSTANT__VARI__
                            (smt__TLA____FunApp smt__VARIABLE__sent____prime
                              smt__CONSTANT__VARJ__)))))))))))))
    :named |Goal|))

(check-sat)
(exit)
