;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Node_,
;;	       NEW CONSTANT CONSTANT_Quorum_,
;;	       NEW CONSTANT CONSTANT_Value_,
;;	       NEW VARIABLE VARIABLE_vote_request_msg_,
;;	       NEW VARIABLE VARIABLE_voted_,
;;	       NEW VARIABLE VARIABLE_vote_msg_,
;;	       NEW VARIABLE VARIABLE_votes_,
;;	       NEW VARIABLE VARIABLE_leader_,
;;	       NEW VARIABLE VARIABLE_decided_
;;	PROVE  (/\ /\ VARIABLE_vote_request_msg_
;;	              \in SUBSET CONSTANT_Node_ \X CONSTANT_Node_
;;	           /\ VARIABLE_voted_ \in [CONSTANT_Node_ -> BOOLEAN]
;;	           /\ VARIABLE_vote_msg_ \in SUBSET CONSTANT_Node_ \X CONSTANT_Node_
;;	           /\ VARIABLE_votes_ \in [CONSTANT_Node_ -> SUBSET CONSTANT_Node_]
;;	           /\ VARIABLE_leader_ \in [CONSTANT_Node_ -> BOOLEAN]
;;	           /\ VARIABLE_decided_
;;	              \in [CONSTANT_Node_ -> SUBSET CONSTANT_Value_]
;;	        /\ \A CONSTANT_n1_, CONSTANT_n2_ \in CONSTANT_Node_,
;;	              CONSTANT_v1_, CONSTANT_v2_ \in CONSTANT_Value_ :
;;	              CONSTANT_v1_ \in VARIABLE_decided_[CONSTANT_n1_]
;;	              /\ CONSTANT_v2_ \in VARIABLE_decided_[CONSTANT_n2_]
;;	              => CONSTANT_v1_ = CONSTANT_v2_
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                 <<CONSTANT_VARJ_, CONSTANT_VARI_>> \in VARIABLE_vote_msg_
;;	                 \/ ~CONSTANT_VARJ_ \in VARIABLE_votes_[CONSTANT_VARI_]
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \E CONSTANT_QJ_ \in CONSTANT_Quorum_ :
;;	                 \A CONSTANT_VALI_ \in CONSTANT_Value_ :
;;	                    CONSTANT_QJ_ \subseteq VARIABLE_votes_[CONSTANT_VARI_]
;;	                    \/ ~CONSTANT_VALI_ \in VARIABLE_decided_[CONSTANT_VARI_]
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                 VARIABLE_voted_[CONSTANT_VARI_]
;;	                 \/ ~<<CONSTANT_VARI_, CONSTANT_VARJ_>>
;;	                     \in VARIABLE_vote_msg_
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \E CONSTANT_QJ_ \in CONSTANT_Quorum_ :
;;	                 CONSTANT_QJ_ \subseteq VARIABLE_votes_[CONSTANT_VARI_]
;;	                 \/ ~VARIABLE_leader_[CONSTANT_VARI_]
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_VALI_ \in CONSTANT_Value_ :
;;	                 VARIABLE_leader_[CONSTANT_VARI_]
;;	                 \/ ~CONSTANT_VALI_ \in VARIABLE_decided_[CONSTANT_VARI_]
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARK_ \in CONSTANT_Node_ :
;;	                    (CONSTANT_VARI_ = CONSTANT_VARK_
;;	                     /\ VARIABLE_votes_ = VARIABLE_votes_)
;;	                    \/ ~<<CONSTANT_VARJ_, CONSTANT_VARI_>>
;;	                        \in VARIABLE_vote_msg_
;;	                    \/ ~CONSTANT_VARJ_ \in VARIABLE_votes_[CONSTANT_VARK_]
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARK_ \in CONSTANT_Node_ :
;;	                    (CONSTANT_VARJ_ = CONSTANT_VARK_
;;	                     /\ VARIABLE_votes_ = VARIABLE_votes_)
;;	                    \/ ~<<CONSTANT_VARI_, CONSTANT_VARK_>>
;;	                        \in VARIABLE_vote_msg_
;;	                    \/ ~<<CONSTANT_VARI_, CONSTANT_VARJ_>>
;;	                        \in VARIABLE_vote_msg_)
;;	       /\ (\/ \E CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Node_ :
;;	                 /\ ?VARIABLE_vote_request_msg_#prime
;;	                    = VARIABLE_vote_request_msg_
;;	                      \cup {<<CONSTANT_i_, CONSTANT_j_>>}
;;	                 /\ /\ ?VARIABLE_voted_#prime = VARIABLE_voted_
;;	                    /\ ?VARIABLE_vote_msg_#prime = VARIABLE_vote_msg_
;;	                    /\ ?VARIABLE_votes_#prime = VARIABLE_votes_
;;	                    /\ ?VARIABLE_leader_#prime = VARIABLE_leader_
;;	                    /\ ?VARIABLE_decided_#prime = VARIABLE_decided_
;;	           \/ \E CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Node_ :
;;	                 /\ ~VARIABLE_voted_[CONSTANT_i_]
;;	                 /\ <<CONSTANT_j_, CONSTANT_i_>>
;;	                    \in VARIABLE_vote_request_msg_
;;	                 /\ ?VARIABLE_vote_msg_#prime
;;	                    = VARIABLE_vote_msg_ \cup {<<CONSTANT_i_, CONSTANT_j_>>}
;;	                 /\ ?VARIABLE_voted_#prime
;;	                    = [VARIABLE_voted_ EXCEPT ![CONSTANT_i_] = TRUE]
;;	                 /\ \/ ?VARIABLE_vote_request_msg_#prime
;;	                       = VARIABLE_vote_request_msg_
;;	                         \cup {<<CONSTANT_i_, CONSTANT_j_>>}
;;	                    \/ ?VARIABLE_vote_request_msg_#prime
;;	                       = VARIABLE_vote_request_msg_
;;	                         \ {<<CONSTANT_i_, CONSTANT_j_>>}
;;	                 /\ /\ ?VARIABLE_votes_#prime = VARIABLE_votes_
;;	                    /\ ?VARIABLE_leader_#prime = VARIABLE_leader_
;;	                    /\ ?VARIABLE_decided_#prime = VARIABLE_decided_
;;	           \/ \E CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Node_ :
;;	                 /\ <<CONSTANT_j_, CONSTANT_i_>> \in VARIABLE_vote_msg_
;;	                 /\ ?VARIABLE_votes_#prime
;;	                    = [VARIABLE_votes_ EXCEPT
;;	                         ![CONSTANT_i_] = VARIABLE_votes_[CONSTANT_i_]
;;	                                          \cup {CONSTANT_j_}]
;;	                 /\ /\ ?VARIABLE_vote_request_msg_#prime
;;	                       = VARIABLE_vote_request_msg_
;;	                    /\ ?VARIABLE_voted_#prime = VARIABLE_voted_
;;	                    /\ ?VARIABLE_vote_msg_#prime = VARIABLE_vote_msg_
;;	                    /\ ?VARIABLE_leader_#prime = VARIABLE_leader_
;;	                    /\ ?VARIABLE_decided_#prime = VARIABLE_decided_
;;	           \/ \E CONSTANT_i_ \in CONSTANT_Node_,
;;	                 CONSTANT_Q_ \in CONSTANT_Quorum_ :
;;	                 /\ CONSTANT_Q_ \subseteq VARIABLE_votes_[CONSTANT_i_]
;;	                 /\ ?VARIABLE_leader_#prime
;;	                    = [VARIABLE_leader_ EXCEPT ![CONSTANT_i_] = TRUE]
;;	                 /\ /\ ?VARIABLE_vote_request_msg_#prime
;;	                       = VARIABLE_vote_request_msg_
;;	                    /\ ?VARIABLE_voted_#prime = VARIABLE_voted_
;;	                    /\ ?VARIABLE_vote_msg_#prime = VARIABLE_vote_msg_
;;	                    /\ ?VARIABLE_votes_#prime = VARIABLE_votes_
;;	                    /\ ?VARIABLE_decided_#prime = VARIABLE_decided_
;;	           \/ \E CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Node_,
;;	                 CONSTANT_v_ \in CONSTANT_Value_ :
;;	                 /\ VARIABLE_leader_[CONSTANT_i_]
;;	                 /\ VARIABLE_decided_[CONSTANT_i_] = {}
;;	                 /\ ?VARIABLE_decided_#prime
;;	                    = [VARIABLE_decided_ EXCEPT
;;	                         ![CONSTANT_i_] = VARIABLE_decided_[CONSTANT_i_]
;;	                                          \cup {CONSTANT_v_}]
;;	                 /\ /\ ?VARIABLE_vote_request_msg_#prime
;;	                       = VARIABLE_vote_request_msg_
;;	                    /\ ?VARIABLE_voted_#prime = VARIABLE_voted_
;;	                    /\ ?VARIABLE_vote_msg_#prime = VARIABLE_vote_msg_
;;	                    /\ ?VARIABLE_votes_#prime = VARIABLE_votes_
;;	                    /\ ?VARIABLE_leader_#prime = VARIABLE_leader_)
;;	       => (/\ /\ ?VARIABLE_vote_request_msg_#prime
;;	                 \in SUBSET CONSTANT_Node_ \X CONSTANT_Node_
;;	              /\ ?VARIABLE_voted_#prime \in [CONSTANT_Node_ -> BOOLEAN]
;;	              /\ ?VARIABLE_vote_msg_#prime
;;	                 \in SUBSET CONSTANT_Node_ \X CONSTANT_Node_
;;	              /\ ?VARIABLE_votes_#prime
;;	                 \in [CONSTANT_Node_ -> SUBSET CONSTANT_Node_]
;;	              /\ ?VARIABLE_leader_#prime \in [CONSTANT_Node_ -> BOOLEAN]
;;	              /\ ?VARIABLE_decided_#prime
;;	                 \in [CONSTANT_Node_ -> SUBSET CONSTANT_Value_]
;;	           /\ \A CONSTANT_n1_, CONSTANT_n2_ \in CONSTANT_Node_,
;;	                 CONSTANT_v1_, CONSTANT_v2_ \in CONSTANT_Value_ :
;;	                 CONSTANT_v1_ \in ?VARIABLE_decided_#prime[CONSTANT_n1_]
;;	                 /\ CONSTANT_v2_ \in ?VARIABLE_decided_#prime[CONSTANT_n2_]
;;	                 => CONSTANT_v1_ = CONSTANT_v2_
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                    <<CONSTANT_VARJ_, CONSTANT_VARI_>>
;;	                    \in ?VARIABLE_vote_msg_#prime
;;	                    \/ ~CONSTANT_VARJ_
;;	                        \in ?VARIABLE_votes_#prime[CONSTANT_VARI_]
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \E CONSTANT_QJ_ \in CONSTANT_Quorum_ :
;;	                    \A CONSTANT_VALI_ \in CONSTANT_Value_ :
;;	                       CONSTANT_QJ_
;;	                       \subseteq ?VARIABLE_votes_#prime[CONSTANT_VARI_]
;;	                       \/ ~CONSTANT_VALI_
;;	                           \in ?VARIABLE_decided_#prime[CONSTANT_VARI_]
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                    ?VARIABLE_voted_#prime[CONSTANT_VARI_]
;;	                    \/ ~<<CONSTANT_VARI_, CONSTANT_VARJ_>>
;;	                        \in ?VARIABLE_vote_msg_#prime
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \E CONSTANT_QJ_ \in CONSTANT_Quorum_ :
;;	                    CONSTANT_QJ_
;;	                    \subseteq ?VARIABLE_votes_#prime[CONSTANT_VARI_]
;;	                    \/ ~?VARIABLE_leader_#prime[CONSTANT_VARI_]
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VALI_ \in CONSTANT_Value_ :
;;	                    ?VARIABLE_leader_#prime[CONSTANT_VARI_]
;;	                    \/ ~CONSTANT_VALI_
;;	                        \in ?VARIABLE_decided_#prime[CONSTANT_VARI_]
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                    \A CONSTANT_VARK_ \in CONSTANT_Node_ :
;;	                       (CONSTANT_VARI_ = CONSTANT_VARK_
;;	                        /\ ?VARIABLE_votes_#prime = ?VARIABLE_votes_#prime)
;;	                       \/ ~<<CONSTANT_VARJ_, CONSTANT_VARI_>>
;;	                           \in ?VARIABLE_vote_msg_#prime
;;	                       \/ ~CONSTANT_VARJ_
;;	                           \in ?VARIABLE_votes_#prime[CONSTANT_VARK_]
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                    \A CONSTANT_VARK_ \in CONSTANT_Node_ :
;;	                       (CONSTANT_VARJ_ = CONSTANT_VARK_
;;	                        /\ ?VARIABLE_votes_#prime = ?VARIABLE_votes_#prime)
;;	                       \/ ~<<CONSTANT_VARI_, CONSTANT_VARK_>>
;;	                           \in ?VARIABLE_vote_msg_#prime
;;	                       \/ ~<<CONSTANT_VARI_, CONSTANT_VARJ_>>
;;	                           \in ?VARIABLE_vote_msg_#prime)
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./29_consensus_epr.tla", line 153, characters 53-54

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

(declare-fun smt__TLA____IntRange (Idv Idv) Idv)

(declare-fun smt__TLA____IntSet () Idv)

(declare-fun smt__TLA____Len (Idv) Idv)

(declare-fun smt__TLA____Mem (Idv Idv) Bool)

(declare-fun smt__TLA____NatSet () Idv)

(declare-fun smt__TLA____Product__2 (Idv Idv) Idv)

(declare-fun smt__TLA____Proj__Int (Idv) Int)

(declare-fun smt__TLA____Seq (Idv) Idv)

(declare-fun smt__TLA____SetEnum__0 () Idv)

(declare-fun smt__TLA____SetEnum__1 (Idv) Idv)

(declare-fun smt__TLA____SetEnum__2 (Idv Idv) Idv)

(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLA____SetMinus (Idv Idv) Idv)

(declare-fun smt__TLA____Subset (Idv) Idv)

(declare-fun smt__TLA____SubsetEq (Idv Idv) Bool)

(declare-fun smt__TLA____Tt__Idv () Idv)

(declare-fun smt__TLA____Tuple__2 (Idv Idv) Idv)

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

;; Axiom: SeqSetIntro
(assert
  (!
    (forall ((smt__a Idv) (smt__s Idv))
      (!
        (=>
          (and (smt__TLA____FunIsafcn smt__s)
            (>= (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 0)
            (forall ((smt__i Idv))
              (= (smt__TLA____Mem smt__i (smt__TLA____FunDom smt__s))
                (and (smt__TLA____Mem smt__i smt__TLA____IntSet)
                  (<= 1 (smt__TLA____Proj__Int smt__i))
                  (<= (smt__TLA____Proj__Int smt__i)
                    (smt__TLA____Proj__Int (smt__TLA____Len smt__s))))))
            (forall ((smt__i Int))
              (=>
                (and (<= 1 smt__i)
                  (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s))))
                (smt__TLA____Mem
                  (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i))
                  smt__a))))
          (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)))
        :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)))))
    :named |SeqSetIntro|))

;; Axiom: SetSetElim1
(assert
  (!
    (forall ((smt__a Idv) (smt__s Idv))
      (!
        (=> (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))
          (and (smt__TLA____FunIsafcn smt__s)
            (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet)
            (= (smt__TLA____FunDom smt__s)
              (smt__TLA____IntRange (smt__TLA____Cast__Int 1)
                (smt__TLA____Len smt__s)))))
        :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)))))
    :named |SetSetElim1|))

;; Axiom: SetSetElim2
(assert
  (!
    (forall ((smt__a Idv) (smt__s Idv) (smt__i Int))
      (!
        (=>
          (and (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))
            (<= 1 smt__i)
            (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s))))
          (smt__TLA____Mem
            (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) 
            smt__a))
        :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))
                   (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)))))
    :named |SetSetElim2|))

;; Axiom: SeqLenDef
(assert
  (!
    (forall ((smt__s Idv) (smt__z Int))
      (=>
        (and (>= smt__z 0)
          (= (smt__TLA____FunDom smt__s)
            (smt__TLA____IntRange (smt__TLA____Cast__Int 1)
              (smt__TLA____Cast__Int smt__z))))
        (= (smt__TLA____Len smt__s) (smt__TLA____Cast__Int smt__z))))
    :named |SeqLenDef|))

;; Axiom: EnumDefIntro 1
(assert
  (!
    (forall ((smt__a1 Idv))
      (! (smt__TLA____Mem smt__a1 (smt__TLA____SetEnum__1 smt__a1))
        :pattern ((smt__TLA____SetEnum__1 smt__a1)))) :named |EnumDefIntro 1|))

;; Axiom: EnumDefIntro 2
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv))
      (!
        (and
          (smt__TLA____Mem smt__a1 (smt__TLA____SetEnum__2 smt__a1 smt__a2))
          (smt__TLA____Mem smt__a2 (smt__TLA____SetEnum__2 smt__a1 smt__a2)))
        :pattern ((smt__TLA____SetEnum__2 smt__a1 smt__a2))))
    :named |EnumDefIntro 2|))

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

;; Axiom: EnumDefElim 2
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__x Idv))
      (!
        (=> (smt__TLA____Mem smt__x (smt__TLA____SetEnum__2 smt__a1 smt__a2))
          (or (= smt__x smt__a1) (= smt__x smt__a2)))
        :pattern ((smt__TLA____Mem smt__x
                    (smt__TLA____SetEnum__2 smt__a1 smt__a2)))))
    :named |EnumDefElim 2|))

;; Axiom: TupIsafcn 2
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv))
      (! (smt__TLA____FunIsafcn (smt__TLA____Tuple__2 smt__x1 smt__x2))
        :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2))))
    :named |TupIsafcn 2|))

;; Axiom: TupDomDef 2
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv))
      (!
        (= (smt__TLA____FunDom (smt__TLA____Tuple__2 smt__x1 smt__x2))
          (smt__TLA____SetEnum__2 (smt__TLA____Cast__Int 1)
            (smt__TLA____Cast__Int 2)))
        :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2))))
    :named |TupDomDef 2|))

;; Axiom: TupAppDef 2
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv))
      (!
        (and
          (=
            (smt__TLA____FunApp (smt__TLA____Tuple__2 smt__x1 smt__x2)
              (smt__TLA____Cast__Int 1)) smt__x1)
          (=
            (smt__TLA____FunApp (smt__TLA____Tuple__2 smt__x1 smt__x2)
              (smt__TLA____Cast__Int 2)) smt__x2))
        :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2))))
    :named |TupAppDef 2|))

;; Axiom: TupExcept 2 1
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x Idv))
      (!
        (=
          (smt__TLA____FunExcept (smt__TLA____Tuple__2 smt__x1 smt__x2)
            (smt__TLA____Cast__Int 1) smt__x)
          (smt__TLA____Tuple__2 smt__x smt__x2))
        :pattern ((smt__TLA____FunExcept
                    (smt__TLA____Tuple__2 smt__x1 smt__x2)
                    (smt__TLA____Cast__Int 1) smt__x))))
    :named |TupExcept 2 1|))

;; Axiom: TupExcept 2 2
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x Idv))
      (!
        (=
          (smt__TLA____FunExcept (smt__TLA____Tuple__2 smt__x1 smt__x2)
            (smt__TLA____Cast__Int 2) smt__x)
          (smt__TLA____Tuple__2 smt__x1 smt__x))
        :pattern ((smt__TLA____FunExcept
                    (smt__TLA____Tuple__2 smt__x1 smt__x2)
                    (smt__TLA____Cast__Int 2) smt__x))))
    :named |TupExcept 2 2|))

;; Axiom: ProductIntro 2
(assert
  (!
    (forall ((smt__s1 Idv) (smt__s2 Idv) (smt__x1 Idv) (smt__x2 Idv))
      (!
        (=>
          (and (smt__TLA____Mem smt__x1 smt__s1)
            (smt__TLA____Mem smt__x2 smt__s2))
          (smt__TLA____Mem (smt__TLA____Tuple__2 smt__x1 smt__x2)
            (smt__TLA____Product__2 smt__s1 smt__s2)))
        :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2)
                   (smt__TLA____Product__2 smt__s1 smt__s2))))
    :named |ProductIntro 2|))

;; Axiom: ProductElim 2
(assert
  (!
    (forall ((smt__s1 Idv) (smt__s2 Idv) (smt__t Idv))
      (!
        (=> (smt__TLA____Mem smt__t (smt__TLA____Product__2 smt__s1 smt__s2))
          (and
            (= smt__t
              (smt__TLA____Tuple__2
                (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 1))
                (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 2))))
            (smt__TLA____Mem
              (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 1)) smt__s1)
            (smt__TLA____Mem
              (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 2)) smt__s2)))
        :pattern ((smt__TLA____Mem smt__t
                    (smt__TLA____Product__2 smt__s1 smt__s2)))))
    :named |ProductElim 2|))

;; Axiom: SeqTupTyping 2
(assert
  (!
    (forall ((smt__a Idv) (smt__x1 Idv) (smt__x2 Idv))
      (!
        (=>
          (and (smt__TLA____Mem smt__x1 smt__a)
            (smt__TLA____Mem smt__x2 smt__a))
          (smt__TLA____Mem (smt__TLA____Tuple__2 smt__x1 smt__x2)
            (smt__TLA____Seq smt__a)))
        :pattern ((smt__TLA____Mem smt__x1 smt__a)
                   (smt__TLA____Mem smt__x2 smt__a)
                   (smt__TLA____Tuple__2 smt__x1 smt__x2))))
    :named |SeqTupTyping 2|))

;; Axiom: SeqTupLen 2
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv))
      (!
        (= (smt__TLA____Len (smt__TLA____Tuple__2 smt__x1 smt__x2))
          (smt__TLA____Cast__Int 2))
        :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2))))
    :named |SeqTupLen 2|))

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

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

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
              (smt__TLA____Mem smt__VARIABLE__vote__request__msg__
                (smt__TLA____Subset
                  (smt__TLA____Product__2 smt__CONSTANT__Node__
                    smt__CONSTANT__Node__)))
              (smt__TLA____Mem smt__VARIABLE__voted__
                (smt__TLA____FunSet smt__CONSTANT__Node__ smt__TLA____BoolSet))
              (smt__TLA____Mem smt__VARIABLE__vote__msg__
                (smt__TLA____Subset
                  (smt__TLA____Product__2 smt__CONSTANT__Node__
                    smt__CONSTANT__Node__)))
              (smt__TLA____Mem smt__VARIABLE__votes__
                (smt__TLA____FunSet smt__CONSTANT__Node__
                  (smt__TLA____Subset smt__CONSTANT__Node__)))
              (smt__TLA____Mem smt__VARIABLE__leader__
                (smt__TLA____FunSet smt__CONSTANT__Node__ smt__TLA____BoolSet))
              (smt__TLA____Mem smt__VARIABLE__decided__
                (smt__TLA____FunSet smt__CONSTANT__Node__
                  (smt__TLA____Subset smt__CONSTANT__Value__))))
            (forall
              ((smt__CONSTANT__n1__ Idv) (smt__CONSTANT__n2__ Idv)
                (smt__CONSTANT__v1__ Idv) (smt__CONSTANT__v2__ Idv))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__n1__ smt__CONSTANT__Node__)
                  (smt__TLA____Mem smt__CONSTANT__n2__ smt__CONSTANT__Node__)
                  (smt__TLA____Mem smt__CONSTANT__v1__ smt__CONSTANT__Value__)
                  (smt__TLA____Mem smt__CONSTANT__v2__ smt__CONSTANT__Value__))
                (=>
                  (and
                    (smt__TLA____Mem smt__CONSTANT__v1__
                      (smt__TLA____FunApp smt__VARIABLE__decided__
                        smt__CONSTANT__n1__))
                    (smt__TLA____Mem smt__CONSTANT__v2__
                      (smt__TLA____FunApp smt__VARIABLE__decided__
                        smt__CONSTANT__n2__)))
                  (= smt__CONSTANT__v1__ smt__CONSTANT__v2__))))
            (forall ((smt__CONSTANT__VARI__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__VARJ__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__VARJ__
                      smt__CONSTANT__Node__)
                    (or
                      (smt__TLA____Mem
                        (smt__TLA____Tuple__2 smt__CONSTANT__VARJ__
                          smt__CONSTANT__VARI__) smt__VARIABLE__vote__msg__)
                      (not
                        (smt__TLA____Mem smt__CONSTANT__VARJ__
                          (smt__TLA____FunApp smt__VARIABLE__votes__
                            smt__CONSTANT__VARI__))))))))
            (forall ((smt__CONSTANT__VARI__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
                (exists ((smt__CONSTANT__QJ__ Idv))
                  (and
                    (smt__TLA____Mem smt__CONSTANT__QJ__
                      smt__CONSTANT__Quorum__)
                    (forall ((smt__CONSTANT__VALI__ Idv))
                      (=>
                        (smt__TLA____Mem smt__CONSTANT__VALI__
                          smt__CONSTANT__Value__)
                        (or
                          (smt__TLA____SubsetEq smt__CONSTANT__QJ__
                            (smt__TLA____FunApp smt__VARIABLE__votes__
                              smt__CONSTANT__VARI__))
                          (not
                            (smt__TLA____Mem smt__CONSTANT__VALI__
                              (smt__TLA____FunApp smt__VARIABLE__decided__
                                smt__CONSTANT__VARI__))))))))))
            (forall ((smt__CONSTANT__VARI__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__VARJ__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__VARJ__
                      smt__CONSTANT__Node__)
                    (or
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__voted__
                          smt__CONSTANT__VARI__) smt__TLA____Tt__Idv)
                      (not
                        (smt__TLA____Mem
                          (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                            smt__CONSTANT__VARJ__) smt__VARIABLE__vote__msg__)))))))
            (forall ((smt__CONSTANT__VARI__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
                (exists ((smt__CONSTANT__QJ__ Idv))
                  (and
                    (smt__TLA____Mem smt__CONSTANT__QJ__
                      smt__CONSTANT__Quorum__)
                    (or
                      (smt__TLA____SubsetEq smt__CONSTANT__QJ__
                        (smt__TLA____FunApp smt__VARIABLE__votes__
                          smt__CONSTANT__VARI__))
                      (not
                        (=
                          (smt__TLA____FunApp smt__VARIABLE__leader__
                            smt__CONSTANT__VARI__) smt__TLA____Tt__Idv)))))))
            (forall ((smt__CONSTANT__VARI__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__VALI__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__VALI__
                      smt__CONSTANT__Value__)
                    (or
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__leader__
                          smt__CONSTANT__VARI__) smt__TLA____Tt__Idv)
                      (not
                        (smt__TLA____Mem smt__CONSTANT__VALI__
                          (smt__TLA____FunApp smt__VARIABLE__decided__
                            smt__CONSTANT__VARI__))))))))
            (forall ((smt__CONSTANT__VARI__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__VARJ__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__VARJ__
                      smt__CONSTANT__Node__)
                    (forall ((smt__CONSTANT__VARK__ Idv))
                      (=>
                        (smt__TLA____Mem smt__CONSTANT__VARK__
                          smt__CONSTANT__Node__)
                        (or
                          (or
                            (and
                              (= smt__CONSTANT__VARI__ smt__CONSTANT__VARK__)
                              (= smt__VARIABLE__votes__
                                smt__VARIABLE__votes__))
                            (not
                              (smt__TLA____Mem
                                (smt__TLA____Tuple__2 smt__CONSTANT__VARJ__
                                  smt__CONSTANT__VARI__)
                                smt__VARIABLE__vote__msg__)))
                          (not
                            (smt__TLA____Mem smt__CONSTANT__VARJ__
                              (smt__TLA____FunApp smt__VARIABLE__votes__
                                smt__CONSTANT__VARK__))))))))))
            (forall ((smt__CONSTANT__VARI__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__VARJ__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__VARJ__
                      smt__CONSTANT__Node__)
                    (forall ((smt__CONSTANT__VARK__ Idv))
                      (=>
                        (smt__TLA____Mem smt__CONSTANT__VARK__
                          smt__CONSTANT__Node__)
                        (or
                          (or
                            (and
                              (= smt__CONSTANT__VARJ__ smt__CONSTANT__VARK__)
                              (= smt__VARIABLE__votes__
                                smt__VARIABLE__votes__))
                            (not
                              (smt__TLA____Mem
                                (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                                  smt__CONSTANT__VARK__)
                                smt__VARIABLE__vote__msg__)))
                          (not
                            (smt__TLA____Mem
                              (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                                smt__CONSTANT__VARJ__)
                              smt__VARIABLE__vote__msg__))))))))))
          (or
            (exists ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
              (and (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Node__)
                (and
                  (= smt__VARIABLE__vote__request__msg____prime
                    (smt__TLA____Cup smt__VARIABLE__vote__request__msg__
                      (smt__TLA____SetEnum__1
                        (smt__TLA____Tuple__2 smt__CONSTANT__i__
                          smt__CONSTANT__j__))))
                  (and
                    (= smt__VARIABLE__voted____prime smt__VARIABLE__voted__)
                    (= smt__VARIABLE__vote__msg____prime
                      smt__VARIABLE__vote__msg__)
                    (= smt__VARIABLE__votes____prime smt__VARIABLE__votes__)
                    (= smt__VARIABLE__leader____prime smt__VARIABLE__leader__)
                    (= smt__VARIABLE__decided____prime
                      smt__VARIABLE__decided__)))))
            (exists ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
              (and (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Node__)
                (and
                  (not
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__voted__
                        smt__CONSTANT__i__) smt__TLA____Tt__Idv))
                  (smt__TLA____Mem
                    (smt__TLA____Tuple__2 smt__CONSTANT__j__
                      smt__CONSTANT__i__) smt__VARIABLE__vote__request__msg__)
                  (= smt__VARIABLE__vote__msg____prime
                    (smt__TLA____Cup smt__VARIABLE__vote__msg__
                      (smt__TLA____SetEnum__1
                        (smt__TLA____Tuple__2 smt__CONSTANT__i__
                          smt__CONSTANT__j__))))
                  (= smt__VARIABLE__voted____prime
                    (smt__TLA____FunExcept smt__VARIABLE__voted__
                      smt__CONSTANT__i__ (smt__TLA____Cast__Bool true)))
                  (or
                    (= smt__VARIABLE__vote__request__msg____prime
                      (smt__TLA____Cup smt__VARIABLE__vote__request__msg__
                        (smt__TLA____SetEnum__1
                          (smt__TLA____Tuple__2 smt__CONSTANT__i__
                            smt__CONSTANT__j__))))
                    (= smt__VARIABLE__vote__request__msg____prime
                      (smt__TLA____SetMinus
                        smt__VARIABLE__vote__request__msg__
                        (smt__TLA____SetEnum__1
                          (smt__TLA____Tuple__2 smt__CONSTANT__i__
                            smt__CONSTANT__j__)))))
                  (and
                    (= smt__VARIABLE__votes____prime smt__VARIABLE__votes__)
                    (= smt__VARIABLE__leader____prime smt__VARIABLE__leader__)
                    (= smt__VARIABLE__decided____prime
                      smt__VARIABLE__decided__)))))
            (exists ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
              (and (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Node__)
                (and
                  (smt__TLA____Mem
                    (smt__TLA____Tuple__2 smt__CONSTANT__j__
                      smt__CONSTANT__i__) smt__VARIABLE__vote__msg__)
                  (= smt__VARIABLE__votes____prime
                    (smt__TLA____FunExcept smt__VARIABLE__votes__
                      smt__CONSTANT__i__
                      (smt__TLA____Cup
                        (smt__TLA____FunApp smt__VARIABLE__votes__
                          smt__CONSTANT__i__)
                        (smt__TLA____SetEnum__1 smt__CONSTANT__j__))))
                  (and
                    (= smt__VARIABLE__vote__request__msg____prime
                      smt__VARIABLE__vote__request__msg__)
                    (= smt__VARIABLE__voted____prime smt__VARIABLE__voted__)
                    (= smt__VARIABLE__vote__msg____prime
                      smt__VARIABLE__vote__msg__)
                    (= smt__VARIABLE__leader____prime smt__VARIABLE__leader__)
                    (= smt__VARIABLE__decided____prime
                      smt__VARIABLE__decided__)))))
            (exists ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__Q__ Idv))
              (and (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__Q__ smt__CONSTANT__Quorum__)
                (and
                  (smt__TLA____SubsetEq smt__CONSTANT__Q__
                    (smt__TLA____FunApp smt__VARIABLE__votes__
                      smt__CONSTANT__i__))
                  (= smt__VARIABLE__leader____prime
                    (smt__TLA____FunExcept smt__VARIABLE__leader__
                      smt__CONSTANT__i__ (smt__TLA____Cast__Bool true)))
                  (and
                    (= smt__VARIABLE__vote__request__msg____prime
                      smt__VARIABLE__vote__request__msg__)
                    (= smt__VARIABLE__voted____prime smt__VARIABLE__voted__)
                    (= smt__VARIABLE__vote__msg____prime
                      smt__VARIABLE__vote__msg__)
                    (= smt__VARIABLE__votes____prime smt__VARIABLE__votes__)
                    (= smt__VARIABLE__decided____prime
                      smt__VARIABLE__decided__)))))
            (exists
              ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv)
                (smt__CONSTANT__v__ Idv))
              (and (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__v__ smt__CONSTANT__Value__)
                (and
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__leader__
                      smt__CONSTANT__i__) smt__TLA____Tt__Idv)
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__decided__
                      smt__CONSTANT__i__) smt__TLA____SetEnum__0)
                  (= smt__VARIABLE__decided____prime
                    (smt__TLA____FunExcept smt__VARIABLE__decided__
                      smt__CONSTANT__i__
                      (smt__TLA____Cup
                        (smt__TLA____FunApp smt__VARIABLE__decided__
                          smt__CONSTANT__i__)
                        (smt__TLA____SetEnum__1 smt__CONSTANT__v__))))
                  (and
                    (= smt__VARIABLE__vote__request__msg____prime
                      smt__VARIABLE__vote__request__msg__)
                    (= smt__VARIABLE__voted____prime smt__VARIABLE__voted__)
                    (= smt__VARIABLE__vote__msg____prime
                      smt__VARIABLE__vote__msg__)
                    (= smt__VARIABLE__votes____prime smt__VARIABLE__votes__)
                    (= smt__VARIABLE__leader____prime smt__VARIABLE__leader__)))))))
        (and
          (and
            (smt__TLA____Mem smt__VARIABLE__vote__request__msg____prime
              (smt__TLA____Subset
                (smt__TLA____Product__2 smt__CONSTANT__Node__
                  smt__CONSTANT__Node__)))
            (smt__TLA____Mem smt__VARIABLE__voted____prime
              (smt__TLA____FunSet smt__CONSTANT__Node__ smt__TLA____BoolSet))
            (smt__TLA____Mem smt__VARIABLE__vote__msg____prime
              (smt__TLA____Subset
                (smt__TLA____Product__2 smt__CONSTANT__Node__
                  smt__CONSTANT__Node__)))
            (smt__TLA____Mem smt__VARIABLE__votes____prime
              (smt__TLA____FunSet smt__CONSTANT__Node__
                (smt__TLA____Subset smt__CONSTANT__Node__)))
            (smt__TLA____Mem smt__VARIABLE__leader____prime
              (smt__TLA____FunSet smt__CONSTANT__Node__ smt__TLA____BoolSet))
            (smt__TLA____Mem smt__VARIABLE__decided____prime
              (smt__TLA____FunSet smt__CONSTANT__Node__
                (smt__TLA____Subset smt__CONSTANT__Value__))))
          (forall
            ((smt__CONSTANT__n1__ Idv) (smt__CONSTANT__n2__ Idv)
              (smt__CONSTANT__v1__ Idv) (smt__CONSTANT__v2__ Idv))
            (=>
              (and
                (smt__TLA____Mem smt__CONSTANT__n1__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__n2__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__v1__ smt__CONSTANT__Value__)
                (smt__TLA____Mem smt__CONSTANT__v2__ smt__CONSTANT__Value__))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__v1__
                    (smt__TLA____FunApp smt__VARIABLE__decided____prime
                      smt__CONSTANT__n1__))
                  (smt__TLA____Mem smt__CONSTANT__v2__
                    (smt__TLA____FunApp smt__VARIABLE__decided____prime
                      smt__CONSTANT__n2__)))
                (= smt__CONSTANT__v1__ smt__CONSTANT__v2__))))
          (forall ((smt__CONSTANT__VARI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__VARJ__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__VARJ__
                    smt__CONSTANT__Node__)
                  (or
                    (smt__TLA____Mem
                      (smt__TLA____Tuple__2 smt__CONSTANT__VARJ__
                        smt__CONSTANT__VARI__)
                      smt__VARIABLE__vote__msg____prime)
                    (not
                      (smt__TLA____Mem smt__CONSTANT__VARJ__
                        (smt__TLA____FunApp smt__VARIABLE__votes____prime
                          smt__CONSTANT__VARI__))))))))
          (forall ((smt__CONSTANT__VARI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
              (exists ((smt__CONSTANT__QJ__ Idv))
                (and
                  (smt__TLA____Mem smt__CONSTANT__QJ__
                    smt__CONSTANT__Quorum__)
                  (forall ((smt__CONSTANT__VALI__ Idv))
                    (=>
                      (smt__TLA____Mem smt__CONSTANT__VALI__
                        smt__CONSTANT__Value__)
                      (or
                        (smt__TLA____SubsetEq smt__CONSTANT__QJ__
                          (smt__TLA____FunApp smt__VARIABLE__votes____prime
                            smt__CONSTANT__VARI__))
                        (not
                          (smt__TLA____Mem smt__CONSTANT__VALI__
                            (smt__TLA____FunApp
                              smt__VARIABLE__decided____prime
                              smt__CONSTANT__VARI__))))))))))
          (forall ((smt__CONSTANT__VARI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__VARJ__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__VARJ__
                    smt__CONSTANT__Node__)
                  (or
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__voted____prime
                        smt__CONSTANT__VARI__) smt__TLA____Tt__Idv)
                    (not
                      (smt__TLA____Mem
                        (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                          smt__CONSTANT__VARJ__)
                        smt__VARIABLE__vote__msg____prime)))))))
          (forall ((smt__CONSTANT__VARI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
              (exists ((smt__CONSTANT__QJ__ Idv))
                (and
                  (smt__TLA____Mem smt__CONSTANT__QJ__
                    smt__CONSTANT__Quorum__)
                  (or
                    (smt__TLA____SubsetEq smt__CONSTANT__QJ__
                      (smt__TLA____FunApp smt__VARIABLE__votes____prime
                        smt__CONSTANT__VARI__))
                    (not
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__leader____prime
                          smt__CONSTANT__VARI__) smt__TLA____Tt__Idv)))))))
          (forall ((smt__CONSTANT__VARI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__VALI__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__VALI__
                    smt__CONSTANT__Value__)
                  (or
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__leader____prime
                        smt__CONSTANT__VARI__) smt__TLA____Tt__Idv)
                    (not
                      (smt__TLA____Mem smt__CONSTANT__VALI__
                        (smt__TLA____FunApp smt__VARIABLE__decided____prime
                          smt__CONSTANT__VARI__))))))))
          (forall ((smt__CONSTANT__VARI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__VARJ__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__VARJ__
                    smt__CONSTANT__Node__)
                  (forall ((smt__CONSTANT__VARK__ Idv))
                    (=>
                      (smt__TLA____Mem smt__CONSTANT__VARK__
                        smt__CONSTANT__Node__)
                      (or
                        (or
                          (and
                            (= smt__CONSTANT__VARI__ smt__CONSTANT__VARK__)
                            (= smt__VARIABLE__votes____prime
                              smt__VARIABLE__votes____prime))
                          (not
                            (smt__TLA____Mem
                              (smt__TLA____Tuple__2 smt__CONSTANT__VARJ__
                                smt__CONSTANT__VARI__)
                              smt__VARIABLE__vote__msg____prime)))
                        (not
                          (smt__TLA____Mem smt__CONSTANT__VARJ__
                            (smt__TLA____FunApp smt__VARIABLE__votes____prime
                              smt__CONSTANT__VARK__))))))))))
          (forall ((smt__CONSTANT__VARI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__VARJ__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__VARJ__
                    smt__CONSTANT__Node__)
                  (forall ((smt__CONSTANT__VARK__ Idv))
                    (=>
                      (smt__TLA____Mem smt__CONSTANT__VARK__
                        smt__CONSTANT__Node__)
                      (or
                        (or
                          (and
                            (= smt__CONSTANT__VARJ__ smt__CONSTANT__VARK__)
                            (= smt__VARIABLE__votes____prime
                              smt__VARIABLE__votes____prime))
                          (not
                            (smt__TLA____Mem
                              (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                                smt__CONSTANT__VARK__)
                              smt__VARIABLE__vote__msg____prime)))
                        (not
                          (smt__TLA____Mem
                            (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                              smt__CONSTANT__VARJ__)
                            smt__VARIABLE__vote__msg____prime))))))))))))
    :named |Goal|))

(check-sat)
(exit)
