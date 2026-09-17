;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Node_,
;;	       NEW CONSTANT CONSTANT_Quorums_,
;;	       NEW VARIABLE VARIABLE_vote_request_msg_,
;;	       NEW VARIABLE VARIABLE_voted_,
;;	       NEW VARIABLE VARIABLE_vote_msg_,
;;	       NEW VARIABLE VARIABLE_votes_,
;;	       NEW VARIABLE VARIABLE_leader_,
;;	       NEW VARIABLE VARIABLE_voting_quorum_
;;	PROVE  (/\ /\ VARIABLE_vote_request_msg_
;;	              \in [CONSTANT_Node_ \X CONSTANT_Node_ -> BOOLEAN]
;;	           /\ VARIABLE_voted_ \in [CONSTANT_Node_ -> BOOLEAN]
;;	           /\ VARIABLE_vote_msg_
;;	              \in [CONSTANT_Node_ \X CONSTANT_Node_ -> BOOLEAN]
;;	           /\ VARIABLE_votes_
;;	              \in [CONSTANT_Node_ \X CONSTANT_Node_ -> BOOLEAN]
;;	           /\ VARIABLE_leader_ \in [CONSTANT_Node_ -> BOOLEAN]
;;	           /\ VARIABLE_voting_quorum_ \in CONSTANT_Quorums_
;;	        /\ \A CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Node_ :
;;	              VARIABLE_leader_[CONSTANT_i_] /\ VARIABLE_leader_[CONSTANT_j_]
;;	              => CONSTANT_i_ = CONSTANT_j_
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                 VARIABLE_vote_request_msg_[<<CONSTANT_VARI_,
;;	                                              CONSTANT_VARJ_>>]
;;	                 \/ ~VARIABLE_votes_[<<CONSTANT_VARI_, CONSTANT_VARJ_>>]
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                 VARIABLE_vote_msg_[<<CONSTANT_VARI_, CONSTANT_VARJ_>>]
;;	                 \/ ~VARIABLE_votes_[<<CONSTANT_VARJ_, CONSTANT_VARI_>>]
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                 VARIABLE_vote_request_msg_[<<CONSTANT_VARI_,
;;	                                              CONSTANT_VARJ_>>]
;;	                 \/ ~VARIABLE_vote_msg_[<<CONSTANT_VARJ_, CONSTANT_VARI_>>]
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                 VARIABLE_voted_[CONSTANT_VARI_]
;;	                 \/ ~VARIABLE_votes_[<<CONSTANT_VARJ_, CONSTANT_VARI_>>]
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                 VARIABLE_votes_[<<CONSTANT_VARI_, CONSTANT_VARJ_>>]
;;	                 \/ (~CONSTANT_VARJ_ \in VARIABLE_voting_quorum_
;;	                     \/ ~VARIABLE_leader_[CONSTANT_VARI_])
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                 VARIABLE_voted_[CONSTANT_VARI_]
;;	                 \/ ~VARIABLE_vote_msg_[<<CONSTANT_VARI_, CONSTANT_VARJ_>>]
;;	        /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARK_ \in CONSTANT_Node_ :
;;	                    CONSTANT_VARJ_ = CONSTANT_VARK_
;;	                    \/ ~VARIABLE_vote_msg_[<<CONSTANT_VARI_, CONSTANT_VARK_>>]
;;	                    \/ ~VARIABLE_vote_msg_[<<CONSTANT_VARI_, CONSTANT_VARJ_>>])
;;	       /\ (\/ \E CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Node_ :
;;	                 /\ ?VARIABLE_vote_request_msg_#prime
;;	                    = [VARIABLE_vote_request_msg_ EXCEPT
;;	                         ![<<CONSTANT_i_, CONSTANT_j_>>] = TRUE]
;;	                 /\ /\ ?VARIABLE_voted_#prime = VARIABLE_voted_
;;	                    /\ ?VARIABLE_vote_msg_#prime = VARIABLE_vote_msg_
;;	                    /\ ?VARIABLE_votes_#prime = VARIABLE_votes_
;;	                    /\ ?VARIABLE_leader_#prime = VARIABLE_leader_
;;	                    /\ ?VARIABLE_voting_quorum_#prime
;;	                       = VARIABLE_voting_quorum_
;;	           \/ \E CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Node_ :
;;	                 /\ ~VARIABLE_voted_[CONSTANT_i_]
;;	                 /\ VARIABLE_vote_request_msg_[<<CONSTANT_j_, CONSTANT_i_>>]
;;	                 /\ ?VARIABLE_vote_msg_#prime
;;	                    = [VARIABLE_vote_msg_ EXCEPT
;;	                         ![<<CONSTANT_i_, CONSTANT_j_>>] = TRUE]
;;	                 /\ ?VARIABLE_voted_#prime
;;	                    = [VARIABLE_voted_ EXCEPT ![CONSTANT_i_] = TRUE]
;;	                 /\ /\ ?VARIABLE_vote_request_msg_#prime
;;	                       = VARIABLE_vote_request_msg_
;;	                    /\ ?VARIABLE_votes_#prime = VARIABLE_votes_
;;	                    /\ ?VARIABLE_leader_#prime = VARIABLE_leader_
;;	                    /\ ?VARIABLE_voting_quorum_#prime
;;	                       = VARIABLE_voting_quorum_
;;	           \/ \E CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Node_ :
;;	                 /\ VARIABLE_vote_msg_[<<CONSTANT_j_, CONSTANT_i_>>]
;;	                 /\ ?VARIABLE_votes_#prime
;;	                    = [VARIABLE_votes_ EXCEPT
;;	                         ![<<CONSTANT_i_, CONSTANT_j_>>] = TRUE]
;;	                 /\ /\ ?VARIABLE_vote_request_msg_#prime
;;	                       = VARIABLE_vote_request_msg_
;;	                    /\ ?VARIABLE_vote_msg_#prime = VARIABLE_vote_msg_
;;	                    /\ ?VARIABLE_voted_#prime = VARIABLE_voted_
;;	                    /\ ?VARIABLE_leader_#prime = VARIABLE_leader_
;;	                    /\ ?VARIABLE_voting_quorum_#prime
;;	                       = VARIABLE_voting_quorum_
;;	           \/ \E CONSTANT_i_ \in CONSTANT_Node_ :
;;	                 \E CONSTANT_Q_ \in CONSTANT_Quorums_ :
;;	                    /\ \A CONSTANT_v_ \in CONSTANT_Q_ :
;;	                          VARIABLE_votes_[<<CONSTANT_i_, CONSTANT_v_>>]
;;	                    /\ ?VARIABLE_voting_quorum_#prime = CONSTANT_Q_
;;	                    /\ /\ ?VARIABLE_vote_request_msg_#prime
;;	                          = VARIABLE_vote_request_msg_
;;	                       /\ ?VARIABLE_vote_msg_#prime = VARIABLE_vote_msg_
;;	                       /\ ?VARIABLE_votes_#prime = VARIABLE_votes_
;;	                       /\ ?VARIABLE_voted_#prime = VARIABLE_voted_
;;	                       /\ ?VARIABLE_leader_#prime = VARIABLE_leader_
;;	           \/ \E CONSTANT_i_ \in CONSTANT_Node_ :
;;	                 /\ VARIABLE_voting_quorum_ # {}
;;	                 /\ \A CONSTANT_v_ \in VARIABLE_voting_quorum_ :
;;	                       VARIABLE_votes_[<<CONSTANT_i_, CONSTANT_v_>>]
;;	                 /\ ?VARIABLE_leader_#prime
;;	                    = [VARIABLE_leader_ EXCEPT ![CONSTANT_i_] = TRUE]
;;	                 /\ /\ ?VARIABLE_vote_request_msg_#prime
;;	                       = VARIABLE_vote_request_msg_
;;	                    /\ ?VARIABLE_vote_msg_#prime = VARIABLE_vote_msg_
;;	                    /\ ?VARIABLE_voted_#prime = VARIABLE_voted_
;;	                    /\ ?VARIABLE_votes_#prime = VARIABLE_votes_
;;	                    /\ ?VARIABLE_voting_quorum_#prime
;;	                       = VARIABLE_voting_quorum_)
;;	       => (/\ /\ ?VARIABLE_vote_request_msg_#prime
;;	                 \in [CONSTANT_Node_ \X CONSTANT_Node_ -> BOOLEAN]
;;	              /\ ?VARIABLE_voted_#prime \in [CONSTANT_Node_ -> BOOLEAN]
;;	              /\ ?VARIABLE_vote_msg_#prime
;;	                 \in [CONSTANT_Node_ \X CONSTANT_Node_ -> BOOLEAN]
;;	              /\ ?VARIABLE_votes_#prime
;;	                 \in [CONSTANT_Node_ \X CONSTANT_Node_ -> BOOLEAN]
;;	              /\ ?VARIABLE_leader_#prime \in [CONSTANT_Node_ -> BOOLEAN]
;;	              /\ ?VARIABLE_voting_quorum_#prime \in CONSTANT_Quorums_
;;	           /\ \A CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Node_ :
;;	                 ?VARIABLE_leader_#prime[CONSTANT_i_]
;;	                 /\ ?VARIABLE_leader_#prime[CONSTANT_j_]
;;	                 => CONSTANT_i_ = CONSTANT_j_
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                    ?VARIABLE_vote_request_msg_#prime[<<CONSTANT_VARI_,
;;	                                                        CONSTANT_VARJ_>>]
;;	                    \/ ~?VARIABLE_votes_#prime[<<CONSTANT_VARI_,
;;	                                                 CONSTANT_VARJ_>>]
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                    ?VARIABLE_vote_msg_#prime[<<CONSTANT_VARI_,
;;	                                                CONSTANT_VARJ_>>]
;;	                    \/ ~?VARIABLE_votes_#prime[<<CONSTANT_VARJ_,
;;	                                                 CONSTANT_VARI_>>]
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                    ?VARIABLE_vote_request_msg_#prime[<<CONSTANT_VARI_,
;;	                                                        CONSTANT_VARJ_>>]
;;	                    \/ ~?VARIABLE_vote_msg_#prime[<<CONSTANT_VARJ_,
;;	                                                    CONSTANT_VARI_>>]
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                    ?VARIABLE_voted_#prime[CONSTANT_VARI_]
;;	                    \/ ~?VARIABLE_votes_#prime[<<CONSTANT_VARJ_,
;;	                                                 CONSTANT_VARI_>>]
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                    ?VARIABLE_votes_#prime[<<CONSTANT_VARI_, CONSTANT_VARJ_>>]
;;	                    \/ (~CONSTANT_VARJ_ \in ?VARIABLE_voting_quorum_#prime
;;	                        \/ ~?VARIABLE_leader_#prime[CONSTANT_VARI_])
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                    ?VARIABLE_voted_#prime[CONSTANT_VARI_]
;;	                    \/ ~?VARIABLE_vote_msg_#prime[<<CONSTANT_VARI_,
;;	                                                    CONSTANT_VARJ_>>]
;;	           /\ \A CONSTANT_VARI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_VARJ_ \in CONSTANT_Node_ :
;;	                    \A CONSTANT_VARK_ \in CONSTANT_Node_ :
;;	                       CONSTANT_VARJ_ = CONSTANT_VARK_
;;	                       \/ ~?VARIABLE_vote_msg_#prime[<<CONSTANT_VARI_,
;;	                                                       CONSTANT_VARK_>>]
;;	                       \/ ~?VARIABLE_vote_msg_#prime[<<CONSTANT_VARI_,
;;	                                                       CONSTANT_VARJ_>>])
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./15_consensus_wo_decide.tla", line 157, characters 1-2

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____BoolSet () Idv)

(declare-fun smt__TLA____Cast__Bool (Bool) Idv)

(declare-fun smt__TLA____Cast__Int (Int) Idv)

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

(declare-fun smt__TLA____SetEnum__2 (Idv Idv) Idv)

(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (Idv
  Idv) Bool)

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

(declare-fun smt__CONSTANT__Node__ () Idv)

(declare-fun smt__CONSTANT__Quorums__ () Idv)

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

(declare-fun smt__VARIABLE__voting__quorum__ () Idv)

(declare-fun smt__VARIABLE__voting__quorum____prime () Idv)

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
                (smt__TLA____FunSet
                  (smt__TLA____Product__2 smt__CONSTANT__Node__
                    smt__CONSTANT__Node__) smt__TLA____BoolSet))
              (smt__TLA____Mem smt__VARIABLE__voted__
                (smt__TLA____FunSet smt__CONSTANT__Node__ smt__TLA____BoolSet))
              (smt__TLA____Mem smt__VARIABLE__vote__msg__
                (smt__TLA____FunSet
                  (smt__TLA____Product__2 smt__CONSTANT__Node__
                    smt__CONSTANT__Node__) smt__TLA____BoolSet))
              (smt__TLA____Mem smt__VARIABLE__votes__
                (smt__TLA____FunSet
                  (smt__TLA____Product__2 smt__CONSTANT__Node__
                    smt__CONSTANT__Node__) smt__TLA____BoolSet))
              (smt__TLA____Mem smt__VARIABLE__leader__
                (smt__TLA____FunSet smt__CONSTANT__Node__ smt__TLA____BoolSet))
              (smt__TLA____Mem smt__VARIABLE__voting__quorum__
                smt__CONSTANT__Quorums__))
            (forall ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Node__)
                  (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Node__))
                (=>
                  (and
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__leader__
                        smt__CONSTANT__i__) smt__TLA____Tt__Idv)
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__leader__
                        smt__CONSTANT__j__) smt__TLA____Tt__Idv))
                  (= smt__CONSTANT__i__ smt__CONSTANT__j__))))
            (forall ((smt__CONSTANT__VARI__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__VARJ__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__VARJ__
                      smt__CONSTANT__Node__)
                    (or
                      (=
                        (smt__TLA____FunApp
                          smt__VARIABLE__vote__request__msg__
                          (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                            smt__CONSTANT__VARJ__)) smt__TLA____Tt__Idv)
                      (not
                        (=
                          (smt__TLA____FunApp smt__VARIABLE__votes__
                            (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                              smt__CONSTANT__VARJ__)) smt__TLA____Tt__Idv)))))))
            (forall ((smt__CONSTANT__VARI__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__VARJ__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__VARJ__
                      smt__CONSTANT__Node__)
                    (or
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__vote__msg__
                          (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                            smt__CONSTANT__VARJ__)) smt__TLA____Tt__Idv)
                      (not
                        (=
                          (smt__TLA____FunApp smt__VARIABLE__votes__
                            (smt__TLA____Tuple__2 smt__CONSTANT__VARJ__
                              smt__CONSTANT__VARI__)) smt__TLA____Tt__Idv)))))))
            (forall ((smt__CONSTANT__VARI__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__VARJ__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__VARJ__
                      smt__CONSTANT__Node__)
                    (or
                      (=
                        (smt__TLA____FunApp
                          smt__VARIABLE__vote__request__msg__
                          (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                            smt__CONSTANT__VARJ__)) smt__TLA____Tt__Idv)
                      (not
                        (=
                          (smt__TLA____FunApp smt__VARIABLE__vote__msg__
                            (smt__TLA____Tuple__2 smt__CONSTANT__VARJ__
                              smt__CONSTANT__VARI__)) smt__TLA____Tt__Idv)))))))
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
                        (=
                          (smt__TLA____FunApp smt__VARIABLE__votes__
                            (smt__TLA____Tuple__2 smt__CONSTANT__VARJ__
                              smt__CONSTANT__VARI__)) smt__TLA____Tt__Idv)))))))
            (forall ((smt__CONSTANT__VARI__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__VARJ__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__VARJ__
                      smt__CONSTANT__Node__)
                    (or
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__votes__
                          (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                            smt__CONSTANT__VARJ__)) smt__TLA____Tt__Idv)
                      (or
                        (not
                          (smt__TLA____Mem smt__CONSTANT__VARJ__
                            smt__VARIABLE__voting__quorum__))
                        (not
                          (=
                            (smt__TLA____FunApp smt__VARIABLE__leader__
                              smt__CONSTANT__VARI__) smt__TLA____Tt__Idv))))))))
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
                        (=
                          (smt__TLA____FunApp smt__VARIABLE__vote__msg__
                            (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                              smt__CONSTANT__VARJ__)) smt__TLA____Tt__Idv)))))))
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
                          (or (= smt__CONSTANT__VARJ__ smt__CONSTANT__VARK__)
                            (not
                              (=
                                (smt__TLA____FunApp
                                  smt__VARIABLE__vote__msg__
                                  (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                                    smt__CONSTANT__VARK__))
                                smt__TLA____Tt__Idv)))
                          (not
                            (=
                              (smt__TLA____FunApp smt__VARIABLE__vote__msg__
                                (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                                  smt__CONSTANT__VARJ__)) smt__TLA____Tt__Idv))))))))))
          (or
            (exists ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
              (and (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Node__)
                (and
                  (= smt__VARIABLE__vote__request__msg____prime
                    (smt__TLA____FunExcept
                      smt__VARIABLE__vote__request__msg__
                      (smt__TLA____Tuple__2 smt__CONSTANT__i__
                        smt__CONSTANT__j__) (smt__TLA____Cast__Bool true)))
                  (and
                    (= smt__VARIABLE__voted____prime smt__VARIABLE__voted__)
                    (= smt__VARIABLE__vote__msg____prime
                      smt__VARIABLE__vote__msg__)
                    (= smt__VARIABLE__votes____prime smt__VARIABLE__votes__)
                    (= smt__VARIABLE__leader____prime smt__VARIABLE__leader__)
                    (= smt__VARIABLE__voting__quorum____prime
                      smt__VARIABLE__voting__quorum__)))))
            (exists ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
              (and (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Node__)
                (and
                  (not
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__voted__
                        smt__CONSTANT__i__) smt__TLA____Tt__Idv))
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__vote__request__msg__
                      (smt__TLA____Tuple__2 smt__CONSTANT__j__
                        smt__CONSTANT__i__)) smt__TLA____Tt__Idv)
                  (= smt__VARIABLE__vote__msg____prime
                    (smt__TLA____FunExcept smt__VARIABLE__vote__msg__
                      (smt__TLA____Tuple__2 smt__CONSTANT__i__
                        smt__CONSTANT__j__) (smt__TLA____Cast__Bool true)))
                  (= smt__VARIABLE__voted____prime
                    (smt__TLA____FunExcept smt__VARIABLE__voted__
                      smt__CONSTANT__i__ (smt__TLA____Cast__Bool true)))
                  (and
                    (= smt__VARIABLE__vote__request__msg____prime
                      smt__VARIABLE__vote__request__msg__)
                    (= smt__VARIABLE__votes____prime smt__VARIABLE__votes__)
                    (= smt__VARIABLE__leader____prime smt__VARIABLE__leader__)
                    (= smt__VARIABLE__voting__quorum____prime
                      smt__VARIABLE__voting__quorum__)))))
            (exists ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
              (and (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Node__)
                (and
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__vote__msg__
                      (smt__TLA____Tuple__2 smt__CONSTANT__j__
                        smt__CONSTANT__i__)) smt__TLA____Tt__Idv)
                  (= smt__VARIABLE__votes____prime
                    (smt__TLA____FunExcept smt__VARIABLE__votes__
                      (smt__TLA____Tuple__2 smt__CONSTANT__i__
                        smt__CONSTANT__j__) (smt__TLA____Cast__Bool true)))
                  (and
                    (= smt__VARIABLE__vote__request__msg____prime
                      smt__VARIABLE__vote__request__msg__)
                    (= smt__VARIABLE__vote__msg____prime
                      smt__VARIABLE__vote__msg__)
                    (= smt__VARIABLE__voted____prime smt__VARIABLE__voted__)
                    (= smt__VARIABLE__leader____prime smt__VARIABLE__leader__)
                    (= smt__VARIABLE__voting__quorum____prime
                      smt__VARIABLE__voting__quorum__)))))
            (exists ((smt__CONSTANT__i__ Idv))
              (and (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Node__)
                (exists ((smt__CONSTANT__Q__ Idv))
                  (and
                    (smt__TLA____Mem smt__CONSTANT__Q__
                      smt__CONSTANT__Quorums__)
                    (and
                      (forall ((smt__CONSTANT__v__ Idv))
                        (=>
                          (smt__TLA____Mem smt__CONSTANT__v__
                            smt__CONSTANT__Q__)
                          (=
                            (smt__TLA____FunApp smt__VARIABLE__votes__
                              (smt__TLA____Tuple__2 smt__CONSTANT__i__
                                smt__CONSTANT__v__)) smt__TLA____Tt__Idv)))
                      (= smt__VARIABLE__voting__quorum____prime
                        smt__CONSTANT__Q__)
                      (and
                        (= smt__VARIABLE__vote__request__msg____prime
                          smt__VARIABLE__vote__request__msg__)
                        (= smt__VARIABLE__vote__msg____prime
                          smt__VARIABLE__vote__msg__)
                        (= smt__VARIABLE__votes____prime
                          smt__VARIABLE__votes__)
                        (= smt__VARIABLE__voted____prime
                          smt__VARIABLE__voted__)
                        (= smt__VARIABLE__leader____prime
                          smt__VARIABLE__leader__)))))))
            (exists ((smt__CONSTANT__i__ Idv))
              (and (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Node__)
                (and
                  (not
                    (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__
                      smt__VARIABLE__voting__quorum__ smt__TLA____SetEnum__0))
                  (forall ((smt__CONSTANT__v__ Idv))
                    (=>
                      (smt__TLA____Mem smt__CONSTANT__v__
                        smt__VARIABLE__voting__quorum__)
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__votes__
                          (smt__TLA____Tuple__2 smt__CONSTANT__i__
                            smt__CONSTANT__v__)) smt__TLA____Tt__Idv)))
                  (= smt__VARIABLE__leader____prime
                    (smt__TLA____FunExcept smt__VARIABLE__leader__
                      smt__CONSTANT__i__ (smt__TLA____Cast__Bool true)))
                  (and
                    (= smt__VARIABLE__vote__request__msg____prime
                      smt__VARIABLE__vote__request__msg__)
                    (= smt__VARIABLE__vote__msg____prime
                      smt__VARIABLE__vote__msg__)
                    (= smt__VARIABLE__voted____prime smt__VARIABLE__voted__)
                    (= smt__VARIABLE__votes____prime smt__VARIABLE__votes__)
                    (= smt__VARIABLE__voting__quorum____prime
                      smt__VARIABLE__voting__quorum__)))))))
        (and
          (and
            (smt__TLA____Mem smt__VARIABLE__vote__request__msg____prime
              (smt__TLA____FunSet
                (smt__TLA____Product__2 smt__CONSTANT__Node__
                  smt__CONSTANT__Node__) smt__TLA____BoolSet))
            (smt__TLA____Mem smt__VARIABLE__voted____prime
              (smt__TLA____FunSet smt__CONSTANT__Node__ smt__TLA____BoolSet))
            (smt__TLA____Mem smt__VARIABLE__vote__msg____prime
              (smt__TLA____FunSet
                (smt__TLA____Product__2 smt__CONSTANT__Node__
                  smt__CONSTANT__Node__) smt__TLA____BoolSet))
            (smt__TLA____Mem smt__VARIABLE__votes____prime
              (smt__TLA____FunSet
                (smt__TLA____Product__2 smt__CONSTANT__Node__
                  smt__CONSTANT__Node__) smt__TLA____BoolSet))
            (smt__TLA____Mem smt__VARIABLE__leader____prime
              (smt__TLA____FunSet smt__CONSTANT__Node__ smt__TLA____BoolSet))
            (smt__TLA____Mem smt__VARIABLE__voting__quorum____prime
              smt__CONSTANT__Quorums__))
          (forall ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
            (=>
              (and (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Node__))
              (=>
                (and
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__leader____prime
                      smt__CONSTANT__i__) smt__TLA____Tt__Idv)
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__leader____prime
                      smt__CONSTANT__j__) smt__TLA____Tt__Idv))
                (= smt__CONSTANT__i__ smt__CONSTANT__j__))))
          (forall ((smt__CONSTANT__VARI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__VARJ__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__VARJ__
                    smt__CONSTANT__Node__)
                  (or
                    (=
                      (smt__TLA____FunApp
                        smt__VARIABLE__vote__request__msg____prime
                        (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                          smt__CONSTANT__VARJ__)) smt__TLA____Tt__Idv)
                    (not
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__votes____prime
                          (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                            smt__CONSTANT__VARJ__)) smt__TLA____Tt__Idv)))))))
          (forall ((smt__CONSTANT__VARI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__VARJ__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__VARJ__
                    smt__CONSTANT__Node__)
                  (or
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__vote__msg____prime
                        (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                          smt__CONSTANT__VARJ__)) smt__TLA____Tt__Idv)
                    (not
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__votes____prime
                          (smt__TLA____Tuple__2 smt__CONSTANT__VARJ__
                            smt__CONSTANT__VARI__)) smt__TLA____Tt__Idv)))))))
          (forall ((smt__CONSTANT__VARI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__VARJ__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__VARJ__
                    smt__CONSTANT__Node__)
                  (or
                    (=
                      (smt__TLA____FunApp
                        smt__VARIABLE__vote__request__msg____prime
                        (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                          smt__CONSTANT__VARJ__)) smt__TLA____Tt__Idv)
                    (not
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__vote__msg____prime
                          (smt__TLA____Tuple__2 smt__CONSTANT__VARJ__
                            smt__CONSTANT__VARI__)) smt__TLA____Tt__Idv)))))))
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
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__votes____prime
                          (smt__TLA____Tuple__2 smt__CONSTANT__VARJ__
                            smt__CONSTANT__VARI__)) smt__TLA____Tt__Idv)))))))
          (forall ((smt__CONSTANT__VARI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__VARI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__VARJ__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__VARJ__
                    smt__CONSTANT__Node__)
                  (or
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__votes____prime
                        (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                          smt__CONSTANT__VARJ__)) smt__TLA____Tt__Idv)
                    (or
                      (not
                        (smt__TLA____Mem smt__CONSTANT__VARJ__
                          smt__VARIABLE__voting__quorum____prime))
                      (not
                        (=
                          (smt__TLA____FunApp smt__VARIABLE__leader____prime
                            smt__CONSTANT__VARI__) smt__TLA____Tt__Idv))))))))
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
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__vote__msg____prime
                          (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                            smt__CONSTANT__VARJ__)) smt__TLA____Tt__Idv)))))))
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
                        (or (= smt__CONSTANT__VARJ__ smt__CONSTANT__VARK__)
                          (not
                            (=
                              (smt__TLA____FunApp
                                smt__VARIABLE__vote__msg____prime
                                (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                                  smt__CONSTANT__VARK__)) smt__TLA____Tt__Idv)))
                        (not
                          (=
                            (smt__TLA____FunApp
                              smt__VARIABLE__vote__msg____prime
                              (smt__TLA____Tuple__2 smt__CONSTANT__VARI__
                                smt__CONSTANT__VARJ__)) smt__TLA____Tt__Idv))))))))))))
    :named |Goal|))

(check-sat)
(exit)
