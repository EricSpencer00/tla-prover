;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Acceptor_,
;;	       NEW CONSTANT CONSTANT_Quorum_,
;;	       NEW CONSTANT CONSTANT_Proposer_,
;;	       NEW VARIABLE VARIABLE_start_,
;;	       NEW VARIABLE VARIABLE_promise_,
;;	       NEW VARIABLE VARIABLE_leader_
;;	PROVE  (/\ /\ VARIABLE_start_ \in SUBSET CONSTANT_Proposer_
;;	           /\ VARIABLE_promise_
;;	              \in SUBSET CONSTANT_Acceptor_ \X CONSTANT_Proposer_
;;	           /\ VARIABLE_leader_ \in SUBSET CONSTANT_Proposer_
;;	        /\ \A CONSTANT_pi_, CONSTANT_pj_ \in CONSTANT_Proposer_ :
;;	              CONSTANT_pi_ \in VARIABLE_leader_
;;	              /\ CONSTANT_pj_ \in VARIABLE_leader_
;;	              => CONSTANT_pi_ = CONSTANT_pj_
;;	        /\ \A CONSTANT_VARS_ \in CONSTANT_Acceptor_ :
;;	              \A CONSTANT_VARPA_ \in CONSTANT_Proposer_ :
;;	                 CONSTANT_VARPA_ \in VARIABLE_start_
;;	                 \/ ~<<CONSTANT_VARS_, CONSTANT_VARPA_>>
;;	                     \in VARIABLE_promise_
;;	        /\ \A CONSTANT_VARPA_ \in CONSTANT_Proposer_ :
;;	              \E CONSTANT_VARQ_ \in CONSTANT_Quorum_ :
;;	                 (\A CONSTANT_a_ \in CONSTANT_VARQ_ :
;;	                     <<CONSTANT_a_, CONSTANT_VARPA_>> \in VARIABLE_promise_)
;;	                 \/ ~CONSTANT_VARPA_ \in VARIABLE_leader_
;;	        /\ \A CONSTANT_VARS_ \in CONSTANT_Acceptor_ :
;;	              \A CONSTANT_VARPA_ \in CONSTANT_Proposer_ :
;;	                 \A CONSTANT_VARPB_ \in CONSTANT_Proposer_ :
;;	                    (CONSTANT_VARPA_ = CONSTANT_VARPB_
;;	                     /\ VARIABLE_promise_ = VARIABLE_promise_)
;;	                    \/ ~<<CONSTANT_VARS_, CONSTANT_VARPA_>>
;;	                        \in VARIABLE_promise_
;;	                    \/ ~<<CONSTANT_VARS_, CONSTANT_VARPB_>>
;;	                        \in VARIABLE_promise_)
;;	       /\ (\/ \E CONSTANT_p_ \in CONSTANT_Proposer_ :
;;	                 /\ ?VARIABLE_start_#prime
;;	                    = VARIABLE_start_ \cup {CONSTANT_p_}
;;	                 /\ /\ ?VARIABLE_promise_#prime = VARIABLE_promise_
;;	                    /\ ?VARIABLE_leader_#prime = VARIABLE_leader_
;;	           \/ \E CONSTANT_a_ \in CONSTANT_Acceptor_,
;;	                 CONSTANT_p_ \in CONSTANT_Proposer_ :
;;	                 /\ CONSTANT_p_ \in VARIABLE_start_
;;	                 /\ \A CONSTANT_p__1 \in CONSTANT_Proposer_ :
;;	                       <<CONSTANT_a_, CONSTANT_p__1>>
;;	                       \notin VARIABLE_promise_
;;	                 /\ ?VARIABLE_promise_#prime
;;	                    = VARIABLE_promise_ \cup {<<CONSTANT_a_, CONSTANT_p_>>}
;;	                 /\ /\ ?VARIABLE_start_#prime = VARIABLE_start_
;;	                    /\ ?VARIABLE_leader_#prime = VARIABLE_leader_
;;	           \/ \E CONSTANT_p_ \in CONSTANT_Proposer_ :
;;	                 \E CONSTANT_Q_ \in CONSTANT_Quorum_ :
;;	                    /\ \A CONSTANT_a_ \in CONSTANT_Q_ :
;;	                          <<CONSTANT_a_, CONSTANT_p_>> \in VARIABLE_promise_
;;	                    /\ ?VARIABLE_leader_#prime
;;	                       = VARIABLE_leader_ \cup {CONSTANT_p_}
;;	                    /\ /\ ?VARIABLE_start_#prime = VARIABLE_start_
;;	                       /\ ?VARIABLE_promise_#prime = VARIABLE_promise_)
;;	       => (/\ /\ ?VARIABLE_start_#prime \in SUBSET CONSTANT_Proposer_
;;	              /\ ?VARIABLE_promise_#prime
;;	                 \in SUBSET CONSTANT_Acceptor_ \X CONSTANT_Proposer_
;;	              /\ ?VARIABLE_leader_#prime \in SUBSET CONSTANT_Proposer_
;;	           /\ \A CONSTANT_pi_, CONSTANT_pj_ \in CONSTANT_Proposer_ :
;;	                 CONSTANT_pi_ \in ?VARIABLE_leader_#prime
;;	                 /\ CONSTANT_pj_ \in ?VARIABLE_leader_#prime
;;	                 => CONSTANT_pi_ = CONSTANT_pj_
;;	           /\ \A CONSTANT_VARS_ \in CONSTANT_Acceptor_ :
;;	                 \A CONSTANT_VARPA_ \in CONSTANT_Proposer_ :
;;	                    CONSTANT_VARPA_ \in ?VARIABLE_start_#prime
;;	                    \/ ~<<CONSTANT_VARS_, CONSTANT_VARPA_>>
;;	                        \in ?VARIABLE_promise_#prime
;;	           /\ \A CONSTANT_VARPA_ \in CONSTANT_Proposer_ :
;;	                 \E CONSTANT_VARQ_ \in CONSTANT_Quorum_ :
;;	                    (\A CONSTANT_a_ \in CONSTANT_VARQ_ :
;;	                        <<CONSTANT_a_, CONSTANT_VARPA_>>
;;	                        \in ?VARIABLE_promise_#prime)
;;	                    \/ ~CONSTANT_VARPA_ \in ?VARIABLE_leader_#prime
;;	           /\ \A CONSTANT_VARS_ \in CONSTANT_Acceptor_ :
;;	                 \A CONSTANT_VARPA_ \in CONSTANT_Proposer_ :
;;	                    \A CONSTANT_VARPB_ \in CONSTANT_Proposer_ :
;;	                       (CONSTANT_VARPA_ = CONSTANT_VARPB_
;;	                        /\ ?VARIABLE_promise_#prime
;;	                           = ?VARIABLE_promise_#prime)
;;	                       \/ ~<<CONSTANT_VARS_, CONSTANT_VARPA_>>
;;	                           \in ?VARIABLE_promise_#prime
;;	                       \/ ~<<CONSTANT_VARS_, CONSTANT_VARPB_>>
;;	                           \in ?VARIABLE_promise_#prime)
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./22_simple_election.tla", line 78, characters 53-54

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Cast__Int (Int) Idv)

(declare-fun smt__TLA____Cup (Idv Idv) Idv)

(declare-fun smt__TLA____FunApp (Idv Idv) Idv)

(declare-fun smt__TLA____FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA____FunIsafcn (Idv) Bool)

(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)

(declare-fun smt__TLA____IntRange (Idv Idv) Idv)

(declare-fun smt__TLA____IntSet () Idv)

(declare-fun smt__TLA____Len (Idv) Idv)

(declare-fun smt__TLA____Mem (Idv Idv) Bool)

(declare-fun smt__TLA____NatSet () Idv)

(declare-fun smt__TLA____Product__2 (Idv Idv) Idv)

(declare-fun smt__TLA____Proj__Int (Idv) Int)

(declare-fun smt__TLA____Seq (Idv) Idv)

(declare-fun smt__TLA____SetEnum__1 (Idv) Idv)

(declare-fun smt__TLA____SetEnum__2 (Idv Idv) Idv)

(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLA____Subset (Idv) Idv)

(declare-fun smt__TLA____SubsetEq (Idv Idv) Bool)

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

; omitted fact (second-order)

; omitted fact (second-order)

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

(declare-fun smt__CONSTANT__Acceptor__ () Idv)

(declare-fun smt__CONSTANT__Quorum__ () Idv)

(declare-fun smt__CONSTANT__Proposer__ () Idv)

(declare-fun smt__VARIABLE__start__ () Idv)

(declare-fun smt__VARIABLE__start____prime () Idv)

(declare-fun smt__VARIABLE__promise__ () Idv)

(declare-fun smt__VARIABLE__promise____prime () Idv)

(declare-fun smt__VARIABLE__leader__ () Idv)

(declare-fun smt__VARIABLE__leader____prime () Idv)

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
              (smt__TLA____Mem smt__VARIABLE__start__
                (smt__TLA____Subset smt__CONSTANT__Proposer__))
              (smt__TLA____Mem smt__VARIABLE__promise__
                (smt__TLA____Subset
                  (smt__TLA____Product__2 smt__CONSTANT__Acceptor__
                    smt__CONSTANT__Proposer__)))
              (smt__TLA____Mem smt__VARIABLE__leader__
                (smt__TLA____Subset smt__CONSTANT__Proposer__)))
            (forall ((smt__CONSTANT__pi__ Idv) (smt__CONSTANT__pj__ Idv))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__pi__
                    smt__CONSTANT__Proposer__)
                  (smt__TLA____Mem smt__CONSTANT__pj__
                    smt__CONSTANT__Proposer__))
                (=>
                  (and
                    (smt__TLA____Mem smt__CONSTANT__pi__
                      smt__VARIABLE__leader__)
                    (smt__TLA____Mem smt__CONSTANT__pj__
                      smt__VARIABLE__leader__))
                  (= smt__CONSTANT__pi__ smt__CONSTANT__pj__))))
            (forall ((smt__CONSTANT__VARS__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARS__
                  smt__CONSTANT__Acceptor__)
                (forall ((smt__CONSTANT__VARPA__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__VARPA__
                      smt__CONSTANT__Proposer__)
                    (or
                      (smt__TLA____Mem smt__CONSTANT__VARPA__
                        smt__VARIABLE__start__)
                      (not
                        (smt__TLA____Mem
                          (smt__TLA____Tuple__2 smt__CONSTANT__VARS__
                            smt__CONSTANT__VARPA__) smt__VARIABLE__promise__)))))))
            (forall ((smt__CONSTANT__VARPA__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARPA__
                  smt__CONSTANT__Proposer__)
                (exists ((smt__CONSTANT__VARQ__ Idv))
                  (and
                    (smt__TLA____Mem smt__CONSTANT__VARQ__
                      smt__CONSTANT__Quorum__)
                    (or
                      (forall ((smt__CONSTANT__a__ Idv))
                        (=>
                          (smt__TLA____Mem smt__CONSTANT__a__
                            smt__CONSTANT__VARQ__)
                          (smt__TLA____Mem
                            (smt__TLA____Tuple__2 smt__CONSTANT__a__
                              smt__CONSTANT__VARPA__)
                            smt__VARIABLE__promise__)))
                      (not
                        (smt__TLA____Mem smt__CONSTANT__VARPA__
                          smt__VARIABLE__leader__)))))))
            (forall ((smt__CONSTANT__VARS__ Idv))
              (=>
                (smt__TLA____Mem smt__CONSTANT__VARS__
                  smt__CONSTANT__Acceptor__)
                (forall ((smt__CONSTANT__VARPA__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__VARPA__
                      smt__CONSTANT__Proposer__)
                    (forall ((smt__CONSTANT__VARPB__ Idv))
                      (=>
                        (smt__TLA____Mem smt__CONSTANT__VARPB__
                          smt__CONSTANT__Proposer__)
                        (or
                          (or
                            (and
                              (= smt__CONSTANT__VARPA__
                                smt__CONSTANT__VARPB__)
                              (= smt__VARIABLE__promise__
                                smt__VARIABLE__promise__))
                            (not
                              (smt__TLA____Mem
                                (smt__TLA____Tuple__2 smt__CONSTANT__VARS__
                                  smt__CONSTANT__VARPA__)
                                smt__VARIABLE__promise__)))
                          (not
                            (smt__TLA____Mem
                              (smt__TLA____Tuple__2 smt__CONSTANT__VARS__
                                smt__CONSTANT__VARPB__)
                              smt__VARIABLE__promise__))))))))))
          (or
            (exists ((smt__CONSTANT__p__ Idv))
              (and
                (smt__TLA____Mem smt__CONSTANT__p__ smt__CONSTANT__Proposer__)
                (and
                  (= smt__VARIABLE__start____prime
                    (smt__TLA____Cup smt__VARIABLE__start__
                      (smt__TLA____SetEnum__1 smt__CONSTANT__p__)))
                  (and
                    (= smt__VARIABLE__promise____prime
                      smt__VARIABLE__promise__)
                    (= smt__VARIABLE__leader____prime smt__VARIABLE__leader__)))))
            (exists ((smt__CONSTANT__a__ Idv) (smt__CONSTANT__p__ Idv))
              (and
                (smt__TLA____Mem smt__CONSTANT__a__ smt__CONSTANT__Acceptor__)
                (smt__TLA____Mem smt__CONSTANT__p__ smt__CONSTANT__Proposer__)
                (and
                  (smt__TLA____Mem smt__CONSTANT__p__ smt__VARIABLE__start__)
                  (forall ((smt__CONSTANT__p___1 Idv))
                    (=>
                      (smt__TLA____Mem smt__CONSTANT__p___1
                        smt__CONSTANT__Proposer__)
                      (not
                        (smt__TLA____Mem
                          (smt__TLA____Tuple__2 smt__CONSTANT__a__
                            smt__CONSTANT__p___1) smt__VARIABLE__promise__))))
                  (= smt__VARIABLE__promise____prime
                    (smt__TLA____Cup smt__VARIABLE__promise__
                      (smt__TLA____SetEnum__1
                        (smt__TLA____Tuple__2 smt__CONSTANT__a__
                          smt__CONSTANT__p__))))
                  (and
                    (= smt__VARIABLE__start____prime smt__VARIABLE__start__)
                    (= smt__VARIABLE__leader____prime smt__VARIABLE__leader__)))))
            (exists ((smt__CONSTANT__p__ Idv))
              (and
                (smt__TLA____Mem smt__CONSTANT__p__ smt__CONSTANT__Proposer__)
                (exists ((smt__CONSTANT__Q__ Idv))
                  (and
                    (smt__TLA____Mem smt__CONSTANT__Q__
                      smt__CONSTANT__Quorum__)
                    (and
                      (forall ((smt__CONSTANT__a__ Idv))
                        (=>
                          (smt__TLA____Mem smt__CONSTANT__a__
                            smt__CONSTANT__Q__)
                          (smt__TLA____Mem
                            (smt__TLA____Tuple__2 smt__CONSTANT__a__
                              smt__CONSTANT__p__) smt__VARIABLE__promise__)))
                      (= smt__VARIABLE__leader____prime
                        (smt__TLA____Cup smt__VARIABLE__leader__
                          (smt__TLA____SetEnum__1 smt__CONSTANT__p__)))
                      (and
                        (= smt__VARIABLE__start____prime
                          smt__VARIABLE__start__)
                        (= smt__VARIABLE__promise____prime
                          smt__VARIABLE__promise__)))))))))
        (and
          (and
            (smt__TLA____Mem smt__VARIABLE__start____prime
              (smt__TLA____Subset smt__CONSTANT__Proposer__))
            (smt__TLA____Mem smt__VARIABLE__promise____prime
              (smt__TLA____Subset
                (smt__TLA____Product__2 smt__CONSTANT__Acceptor__
                  smt__CONSTANT__Proposer__)))
            (smt__TLA____Mem smt__VARIABLE__leader____prime
              (smt__TLA____Subset smt__CONSTANT__Proposer__)))
          (forall ((smt__CONSTANT__pi__ Idv) (smt__CONSTANT__pj__ Idv))
            (=>
              (and
                (smt__TLA____Mem smt__CONSTANT__pi__
                  smt__CONSTANT__Proposer__)
                (smt__TLA____Mem smt__CONSTANT__pj__
                  smt__CONSTANT__Proposer__))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__pi__
                    smt__VARIABLE__leader____prime)
                  (smt__TLA____Mem smt__CONSTANT__pj__
                    smt__VARIABLE__leader____prime))
                (= smt__CONSTANT__pi__ smt__CONSTANT__pj__))))
          (forall ((smt__CONSTANT__VARS__ Idv))
            (=>
              (smt__TLA____Mem smt__CONSTANT__VARS__
                smt__CONSTANT__Acceptor__)
              (forall ((smt__CONSTANT__VARPA__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__VARPA__
                    smt__CONSTANT__Proposer__)
                  (or
                    (smt__TLA____Mem smt__CONSTANT__VARPA__
                      smt__VARIABLE__start____prime)
                    (not
                      (smt__TLA____Mem
                        (smt__TLA____Tuple__2 smt__CONSTANT__VARS__
                          smt__CONSTANT__VARPA__)
                        smt__VARIABLE__promise____prime)))))))
          (forall ((smt__CONSTANT__VARPA__ Idv))
            (=>
              (smt__TLA____Mem smt__CONSTANT__VARPA__
                smt__CONSTANT__Proposer__)
              (exists ((smt__CONSTANT__VARQ__ Idv))
                (and
                  (smt__TLA____Mem smt__CONSTANT__VARQ__
                    smt__CONSTANT__Quorum__)
                  (or
                    (forall ((smt__CONSTANT__a__ Idv))
                      (=>
                        (smt__TLA____Mem smt__CONSTANT__a__
                          smt__CONSTANT__VARQ__)
                        (smt__TLA____Mem
                          (smt__TLA____Tuple__2 smt__CONSTANT__a__
                            smt__CONSTANT__VARPA__)
                          smt__VARIABLE__promise____prime)))
                    (not
                      (smt__TLA____Mem smt__CONSTANT__VARPA__
                        smt__VARIABLE__leader____prime)))))))
          (forall ((smt__CONSTANT__VARS__ Idv))
            (=>
              (smt__TLA____Mem smt__CONSTANT__VARS__
                smt__CONSTANT__Acceptor__)
              (forall ((smt__CONSTANT__VARPA__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__VARPA__
                    smt__CONSTANT__Proposer__)
                  (forall ((smt__CONSTANT__VARPB__ Idv))
                    (=>
                      (smt__TLA____Mem smt__CONSTANT__VARPB__
                        smt__CONSTANT__Proposer__)
                      (or
                        (or
                          (and
                            (= smt__CONSTANT__VARPA__ smt__CONSTANT__VARPB__)
                            (= smt__VARIABLE__promise____prime
                              smt__VARIABLE__promise____prime))
                          (not
                            (smt__TLA____Mem
                              (smt__TLA____Tuple__2 smt__CONSTANT__VARS__
                                smt__CONSTANT__VARPA__)
                              smt__VARIABLE__promise____prime)))
                        (not
                          (smt__TLA____Mem
                            (smt__TLA____Tuple__2 smt__CONSTANT__VARS__
                              smt__CONSTANT__VARPB__)
                            smt__VARIABLE__promise____prime))))))))))))
    :named |Goal|))

(check-sat)
(exit)
