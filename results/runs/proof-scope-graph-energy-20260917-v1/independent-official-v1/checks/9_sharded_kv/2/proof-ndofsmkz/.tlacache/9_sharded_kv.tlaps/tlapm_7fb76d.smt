;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Key_,
;;	       NEW CONSTANT CONSTANT_Value_,
;;	       NEW CONSTANT CONSTANT_Node_,
;;	       NEW CONSTANT CONSTANT_Nil_,
;;	       NEW VARIABLE VARIABLE_table_,
;;	       NEW VARIABLE VARIABLE_owner_,
;;	       NEW VARIABLE VARIABLE_transfer_msg_
;;	PROVE  (/\ /\ VARIABLE_table_
;;	              \in [CONSTANT_Node_ ->
;;	                     [CONSTANT_Key_ -> CONSTANT_Value_ \cup {CONSTANT_Nil_}]]
;;	           /\ VARIABLE_owner_ \in [CONSTANT_Node_ -> SUBSET CONSTANT_Key_]
;;	           /\ VARIABLE_transfer_msg_
;;	              \in SUBSET CONSTANT_Node_ \X CONSTANT_Key_ \X CONSTANT_Value_
;;	        /\ \A CONSTANT_n1_, CONSTANT_n2_ \in CONSTANT_Node_,
;;	              CONSTANT_k_ \in CONSTANT_Key_,
;;	              CONSTANT_v1_, CONSTANT_v2_ \in CONSTANT_Value_ :
;;	              VARIABLE_table_[CONSTANT_n1_][CONSTANT_k_] = CONSTANT_v1_
;;	              /\ VARIABLE_table_[CONSTANT_n2_][CONSTANT_k_] = CONSTANT_v2_
;;	              => CONSTANT_n1_ = CONSTANT_n2_ /\ CONSTANT_v1_ = CONSTANT_v2_
;;	        /\ \A CONSTANT_NI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_NJ_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_KI_ \in CONSTANT_Key_ :
;;	                    \A CONSTANT_VALI_ \in CONSTANT_Value_ :
;;	                       ~<<CONSTANT_NI_, CONSTANT_KI_, CONSTANT_VALI_>>
;;	                        \in VARIABLE_transfer_msg_
;;	                       \/ ~CONSTANT_KI_ \in VARIABLE_owner_[CONSTANT_NJ_]
;;	        /\ \A CONSTANT_NJ_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_KI_ \in CONSTANT_Key_ :
;;	                 CONSTANT_KI_ \in VARIABLE_owner_[CONSTANT_NJ_]
;;	                 \/ VARIABLE_table_[CONSTANT_NJ_][CONSTANT_KI_]
;;	                    = CONSTANT_Nil_
;;	        /\ \A CONSTANT_NI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_NJ_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_KI_ \in CONSTANT_Key_ :
;;	                    (CONSTANT_NI_ = CONSTANT_NJ_
;;	                     /\ VARIABLE_owner_ = VARIABLE_owner_)
;;	                    \/ ~CONSTANT_KI_ \in VARIABLE_owner_[CONSTANT_NI_]
;;	                    \/ ~CONSTANT_KI_ \in VARIABLE_owner_[CONSTANT_NJ_]
;;	        /\ \A CONSTANT_NI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_NJ_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_KI_ \in CONSTANT_Key_ :
;;	                    \A CONSTANT_VALI_ \in CONSTANT_Value_ :
;;	                       \A CONSTANT_VALJ_ \in CONSTANT_Value_ :
;;	                          (CONSTANT_NI_ = CONSTANT_NJ_
;;	                           /\ VARIABLE_owner_ = VARIABLE_owner_)
;;	                          \/ (~<<CONSTANT_NI_, CONSTANT_KI_, CONSTANT_VALJ_>>
;;	                               \in VARIABLE_transfer_msg_
;;	                              \/ ~<<CONSTANT_NJ_, CONSTANT_KI_,
;;	                                    CONSTANT_VALI_>>
;;	                                  \in VARIABLE_transfer_msg_)
;;	        /\ \A CONSTANT_NI_ \in CONSTANT_Node_ :
;;	              \A CONSTANT_KI_ \in CONSTANT_Key_ :
;;	                 \A CONSTANT_VALI_ \in CONSTANT_Value_ :
;;	                    \A CONSTANT_VALJ_ \in CONSTANT_Value_ :
;;	                       (CONSTANT_VALI_ = CONSTANT_VALJ_
;;	                        /\ VARIABLE_owner_ = VARIABLE_owner_)
;;	                       \/ ~<<CONSTANT_NI_, CONSTANT_KI_, CONSTANT_VALJ_>>
;;	                           \in VARIABLE_transfer_msg_
;;	                       \/ ~<<CONSTANT_NI_, CONSTANT_KI_, CONSTANT_VALI_>>
;;	                           \in VARIABLE_transfer_msg_)
;;	       /\ (\/ \E CONSTANT_k_ \in CONSTANT_Key_,
;;	                 CONSTANT_v_ \in CONSTANT_Value_,
;;	                 CONSTANT_n_old_, CONSTANT_n_new_ \in CONSTANT_Node_ :
;;	                 /\ VARIABLE_table_[CONSTANT_n_old_][CONSTANT_k_]
;;	                    = CONSTANT_v_
;;	                 /\ ?VARIABLE_table_#prime
;;	                    = [VARIABLE_table_ EXCEPT
;;	                         ![CONSTANT_n_old_] = [VARIABLE_table_[CONSTANT_n_old_] EXCEPT
;;	                                                 ![CONSTANT_k_] = CONSTANT_Nil_]]
;;	                 /\ ?VARIABLE_owner_#prime
;;	                    = [VARIABLE_owner_ EXCEPT
;;	                         ![CONSTANT_n_old_] = VARIABLE_owner_[CONSTANT_n_old_]
;;	                                              \ {CONSTANT_k_}]
;;	                 /\ ?VARIABLE_transfer_msg_#prime
;;	                    = VARIABLE_transfer_msg_
;;	                      \cup {<<CONSTANT_n_new_, CONSTANT_k_, CONSTANT_v_>>}
;;	           \/ \E CONSTANT_n_ \in CONSTANT_Node_,
;;	                 CONSTANT_k_ \in CONSTANT_Key_,
;;	                 CONSTANT_v_ \in CONSTANT_Value_ :
;;	                 /\ <<CONSTANT_n_, CONSTANT_k_, CONSTANT_v_>>
;;	                    \in VARIABLE_transfer_msg_
;;	                 /\ ?VARIABLE_transfer_msg_#prime
;;	                    = VARIABLE_transfer_msg_
;;	                      \ {<<CONSTANT_n_, CONSTANT_k_, CONSTANT_v_>>}
;;	                 /\ ?VARIABLE_table_#prime
;;	                    = [VARIABLE_table_ EXCEPT
;;	                         ![CONSTANT_n_] = [VARIABLE_table_[CONSTANT_n_] EXCEPT
;;	                                             ![CONSTANT_k_] = CONSTANT_v_]]
;;	                 /\ ?VARIABLE_owner_#prime
;;	                    = [VARIABLE_owner_ EXCEPT
;;	                         ![CONSTANT_n_] = VARIABLE_owner_[CONSTANT_n_]
;;	                                          \cup {CONSTANT_k_}]
;;	           \/ \E CONSTANT_n_ \in CONSTANT_Node_,
;;	                 CONSTANT_k_ \in CONSTANT_Key_,
;;	                 CONSTANT_v_ \in CONSTANT_Value_ :
;;	                 /\ CONSTANT_k_ \in VARIABLE_owner_[CONSTANT_n_]
;;	                 /\ ?VARIABLE_table_#prime
;;	                    = [VARIABLE_table_ EXCEPT
;;	                         ![CONSTANT_n_] = [VARIABLE_table_[CONSTANT_n_] EXCEPT
;;	                                             ![CONSTANT_k_] = CONSTANT_v_]]
;;	                 /\ /\ ?VARIABLE_owner_#prime = VARIABLE_owner_
;;	                    /\ ?VARIABLE_transfer_msg_#prime = VARIABLE_transfer_msg_)
;;	       => (/\ /\ ?VARIABLE_table_#prime
;;	                 \in [CONSTANT_Node_ ->
;;	                        [CONSTANT_Key_ ->
;;	                           CONSTANT_Value_ \cup {CONSTANT_Nil_}]]
;;	              /\ ?VARIABLE_owner_#prime
;;	                 \in [CONSTANT_Node_ -> SUBSET CONSTANT_Key_]
;;	              /\ ?VARIABLE_transfer_msg_#prime
;;	                 \in SUBSET CONSTANT_Node_
;;	                            \X CONSTANT_Key_ \X CONSTANT_Value_
;;	           /\ \A CONSTANT_n1_, CONSTANT_n2_ \in CONSTANT_Node_,
;;	                 CONSTANT_k_ \in CONSTANT_Key_,
;;	                 CONSTANT_v1_, CONSTANT_v2_ \in CONSTANT_Value_ :
;;	                 ?VARIABLE_table_#prime[CONSTANT_n1_][CONSTANT_k_]
;;	                 = CONSTANT_v1_
;;	                 /\ ?VARIABLE_table_#prime[CONSTANT_n2_][CONSTANT_k_]
;;	                    = CONSTANT_v2_
;;	                 => CONSTANT_n1_ = CONSTANT_n2_
;;	                    /\ CONSTANT_v1_ = CONSTANT_v2_
;;	           /\ \A CONSTANT_NI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_NJ_ \in CONSTANT_Node_ :
;;	                    \A CONSTANT_KI_ \in CONSTANT_Key_ :
;;	                       \A CONSTANT_VALI_ \in CONSTANT_Value_ :
;;	                          ~<<CONSTANT_NI_, CONSTANT_KI_, CONSTANT_VALI_>>
;;	                           \in ?VARIABLE_transfer_msg_#prime
;;	                          \/ ~CONSTANT_KI_
;;	                              \in ?VARIABLE_owner_#prime[CONSTANT_NJ_]
;;	           /\ \A CONSTANT_NJ_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_KI_ \in CONSTANT_Key_ :
;;	                    CONSTANT_KI_ \in ?VARIABLE_owner_#prime[CONSTANT_NJ_]
;;	                    \/ ?VARIABLE_table_#prime[CONSTANT_NJ_][CONSTANT_KI_]
;;	                       = CONSTANT_Nil_
;;	           /\ \A CONSTANT_NI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_NJ_ \in CONSTANT_Node_ :
;;	                    \A CONSTANT_KI_ \in CONSTANT_Key_ :
;;	                       (CONSTANT_NI_ = CONSTANT_NJ_
;;	                        /\ ?VARIABLE_owner_#prime = ?VARIABLE_owner_#prime)
;;	                       \/ ~CONSTANT_KI_
;;	                           \in ?VARIABLE_owner_#prime[CONSTANT_NI_]
;;	                       \/ ~CONSTANT_KI_
;;	                           \in ?VARIABLE_owner_#prime[CONSTANT_NJ_]
;;	           /\ \A CONSTANT_NI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_NJ_ \in CONSTANT_Node_ :
;;	                    \A CONSTANT_KI_ \in CONSTANT_Key_ :
;;	                       \A CONSTANT_VALI_ \in CONSTANT_Value_ :
;;	                          \A CONSTANT_VALJ_ \in CONSTANT_Value_ :
;;	                             (CONSTANT_NI_ = CONSTANT_NJ_
;;	                              /\ ?VARIABLE_owner_#prime
;;	                                 = ?VARIABLE_owner_#prime)
;;	                             \/ (~<<CONSTANT_NI_, CONSTANT_KI_,
;;	                                    CONSTANT_VALJ_>>
;;	                                  \in ?VARIABLE_transfer_msg_#prime
;;	                                 \/ ~<<CONSTANT_NJ_, CONSTANT_KI_,
;;	                                       CONSTANT_VALI_>>
;;	                                     \in ?VARIABLE_transfer_msg_#prime)
;;	           /\ \A CONSTANT_NI_ \in CONSTANT_Node_ :
;;	                 \A CONSTANT_KI_ \in CONSTANT_Key_ :
;;	                    \A CONSTANT_VALI_ \in CONSTANT_Value_ :
;;	                       \A CONSTANT_VALJ_ \in CONSTANT_Value_ :
;;	                          (CONSTANT_VALI_ = CONSTANT_VALJ_
;;	                           /\ ?VARIABLE_owner_#prime = ?VARIABLE_owner_#prime)
;;	                          \/ ~<<CONSTANT_NI_, CONSTANT_KI_, CONSTANT_VALJ_>>
;;	                              \in ?VARIABLE_transfer_msg_#prime
;;	                          \/ ~<<CONSTANT_NI_, CONSTANT_KI_, CONSTANT_VALI_>>
;;	                              \in ?VARIABLE_transfer_msg_#prime)
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./9_sharded_kv.tla", line 94, characters 53-54

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

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

(declare-fun smt__TLA____Product__3 (Idv Idv Idv) Idv)

(declare-fun smt__TLA____Proj__Int (Idv) Int)

(declare-fun smt__TLA____Seq (Idv) Idv)

(declare-fun smt__TLA____SetEnum__1 (Idv) Idv)

(declare-fun smt__TLA____SetEnum__3 (Idv Idv Idv) Idv)

(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLA____SetMinus (Idv Idv) Idv)

(declare-fun smt__TLA____Subset (Idv) Idv)

(declare-fun smt__TLA____SubsetEq (Idv Idv) Bool)

(declare-fun smt__TLA____Tuple__3 (Idv Idv Idv) Idv)

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

;; Axiom: EnumDefIntro 3
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv))
      (!
        (and
          (smt__TLA____Mem smt__a1
            (smt__TLA____SetEnum__3 smt__a1 smt__a2 smt__a3))
          (smt__TLA____Mem smt__a2
            (smt__TLA____SetEnum__3 smt__a1 smt__a2 smt__a3))
          (smt__TLA____Mem smt__a3
            (smt__TLA____SetEnum__3 smt__a1 smt__a2 smt__a3)))
        :pattern ((smt__TLA____SetEnum__3 smt__a1 smt__a2 smt__a3))))
    :named |EnumDefIntro 3|))

;; Axiom: EnumDefElim 1
(assert
  (!
    (forall ((smt__a1 Idv) (smt__x Idv))
      (!
        (=> (smt__TLA____Mem smt__x (smt__TLA____SetEnum__1 smt__a1))
          (= smt__x smt__a1))
        :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetEnum__1 smt__a1)))))
    :named |EnumDefElim 1|))

;; Axiom: EnumDefElim 3
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__x Idv))
      (!
        (=>
          (smt__TLA____Mem smt__x
            (smt__TLA____SetEnum__3 smt__a1 smt__a2 smt__a3))
          (or (= smt__x smt__a1) (= smt__x smt__a2) (= smt__x smt__a3)))
        :pattern ((smt__TLA____Mem smt__x
                    (smt__TLA____SetEnum__3 smt__a1 smt__a2 smt__a3)))))
    :named |EnumDefElim 3|))

;; Axiom: TupIsafcn 3
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv))
      (!
        (smt__TLA____FunIsafcn (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3))
        :pattern ((smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3))))
    :named |TupIsafcn 3|))

;; Axiom: TupDomDef 3
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv))
      (!
        (=
          (smt__TLA____FunDom (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3))
          (smt__TLA____SetEnum__3 (smt__TLA____Cast__Int 1)
            (smt__TLA____Cast__Int 2) (smt__TLA____Cast__Int 3)))
        :pattern ((smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3))))
    :named |TupDomDef 3|))

;; Axiom: TupAppDef 3
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv))
      (!
        (and
          (=
            (smt__TLA____FunApp
              (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)
              (smt__TLA____Cast__Int 1)) smt__x1)
          (=
            (smt__TLA____FunApp
              (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)
              (smt__TLA____Cast__Int 2)) smt__x2)
          (=
            (smt__TLA____FunApp
              (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)
              (smt__TLA____Cast__Int 3)) smt__x3))
        :pattern ((smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3))))
    :named |TupAppDef 3|))

;; Axiom: TupExcept 3 1
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x Idv))
      (!
        (=
          (smt__TLA____FunExcept
            (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)
            (smt__TLA____Cast__Int 1) smt__x)
          (smt__TLA____Tuple__3 smt__x smt__x2 smt__x3))
        :pattern ((smt__TLA____FunExcept
                    (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)
                    (smt__TLA____Cast__Int 1) smt__x))))
    :named |TupExcept 3 1|))

;; Axiom: TupExcept 3 2
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x Idv))
      (!
        (=
          (smt__TLA____FunExcept
            (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)
            (smt__TLA____Cast__Int 2) smt__x)
          (smt__TLA____Tuple__3 smt__x1 smt__x smt__x3))
        :pattern ((smt__TLA____FunExcept
                    (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)
                    (smt__TLA____Cast__Int 2) smt__x))))
    :named |TupExcept 3 2|))

;; Axiom: TupExcept 3 3
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x Idv))
      (!
        (=
          (smt__TLA____FunExcept
            (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)
            (smt__TLA____Cast__Int 3) smt__x)
          (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x))
        :pattern ((smt__TLA____FunExcept
                    (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)
                    (smt__TLA____Cast__Int 3) smt__x))))
    :named |TupExcept 3 3|))

;; Axiom: ProductIntro 3
(assert
  (!
    (forall
      ((smt__s1 Idv) (smt__s2 Idv) (smt__s3 Idv) (smt__x1 Idv) (smt__x2 Idv)
        (smt__x3 Idv))
      (!
        (=>
          (and (smt__TLA____Mem smt__x1 smt__s1)
            (smt__TLA____Mem smt__x2 smt__s2)
            (smt__TLA____Mem smt__x3 smt__s3))
          (smt__TLA____Mem (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)
            (smt__TLA____Product__3 smt__s1 smt__s2 smt__s3)))
        :pattern ((smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)
                   (smt__TLA____Product__3 smt__s1 smt__s2 smt__s3))))
    :named |ProductIntro 3|))

;; Axiom: ProductElim 3
(assert
  (!
    (forall ((smt__s1 Idv) (smt__s2 Idv) (smt__s3 Idv) (smt__t Idv))
      (!
        (=>
          (smt__TLA____Mem smt__t
            (smt__TLA____Product__3 smt__s1 smt__s2 smt__s3))
          (and
            (= smt__t
              (smt__TLA____Tuple__3
                (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 1))
                (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 2))
                (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 3))))
            (smt__TLA____Mem
              (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 1)) smt__s1)
            (smt__TLA____Mem
              (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 2)) smt__s2)
            (smt__TLA____Mem
              (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 3)) smt__s3)))
        :pattern ((smt__TLA____Mem smt__t
                    (smt__TLA____Product__3 smt__s1 smt__s2 smt__s3)))))
    :named |ProductElim 3|))

;; Axiom: SeqTupTyping 3
(assert
  (!
    (forall ((smt__a Idv) (smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv))
      (!
        (=>
          (and (smt__TLA____Mem smt__x1 smt__a)
            (smt__TLA____Mem smt__x2 smt__a) (smt__TLA____Mem smt__x3 smt__a))
          (smt__TLA____Mem (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)
            (smt__TLA____Seq smt__a)))
        :pattern ((smt__TLA____Mem smt__x1 smt__a)
                   (smt__TLA____Mem smt__x2 smt__a)
                   (smt__TLA____Mem smt__x3 smt__a)
                   (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3))))
    :named |SeqTupTyping 3|))

;; Axiom: SeqTupLen 3
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv))
      (!
        (= (smt__TLA____Len (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3))
          (smt__TLA____Cast__Int 3))
        :pattern ((smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3))))
    :named |SeqTupLen 3|))

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

(declare-fun smt__CONSTANT__Key__ () Idv)

(declare-fun smt__CONSTANT__Value__ () Idv)

(declare-fun smt__CONSTANT__Node__ () Idv)

(declare-fun smt__CONSTANT__Nil__ () Idv)

(declare-fun smt__VARIABLE__table__ () Idv)

(declare-fun smt__VARIABLE__table____prime () Idv)

(declare-fun smt__VARIABLE__owner__ () Idv)

(declare-fun smt__VARIABLE__owner____prime () Idv)

(declare-fun smt__VARIABLE__transfer__msg__ () Idv)

(declare-fun smt__VARIABLE__transfer__msg____prime () Idv)

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
              (smt__TLA____Mem smt__VARIABLE__table__
                (smt__TLA____FunSet smt__CONSTANT__Node__
                  (smt__TLA____FunSet smt__CONSTANT__Key__
                    (smt__TLA____Cup smt__CONSTANT__Value__
                      (smt__TLA____SetEnum__1 smt__CONSTANT__Nil__)))))
              (smt__TLA____Mem smt__VARIABLE__owner__
                (smt__TLA____FunSet smt__CONSTANT__Node__
                  (smt__TLA____Subset smt__CONSTANT__Key__)))
              (smt__TLA____Mem smt__VARIABLE__transfer__msg__
                (smt__TLA____Subset
                  (smt__TLA____Product__3 smt__CONSTANT__Node__
                    smt__CONSTANT__Key__ smt__CONSTANT__Value__))))
            (forall
              ((smt__CONSTANT__n1__ Idv) (smt__CONSTANT__n2__ Idv)
                (smt__CONSTANT__k__ Idv) (smt__CONSTANT__v1__ Idv)
                (smt__CONSTANT__v2__ Idv))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__n1__ smt__CONSTANT__Node__)
                  (smt__TLA____Mem smt__CONSTANT__n2__ smt__CONSTANT__Node__)
                  (smt__TLA____Mem smt__CONSTANT__k__ smt__CONSTANT__Key__)
                  (smt__TLA____Mem smt__CONSTANT__v1__ smt__CONSTANT__Value__)
                  (smt__TLA____Mem smt__CONSTANT__v2__ smt__CONSTANT__Value__))
                (=>
                  (and
                    (=
                      (smt__TLA____FunApp
                        (smt__TLA____FunApp smt__VARIABLE__table__
                          smt__CONSTANT__n1__) smt__CONSTANT__k__)
                      smt__CONSTANT__v1__)
                    (=
                      (smt__TLA____FunApp
                        (smt__TLA____FunApp smt__VARIABLE__table__
                          smt__CONSTANT__n2__) smt__CONSTANT__k__)
                      smt__CONSTANT__v2__))
                  (and (= smt__CONSTANT__n1__ smt__CONSTANT__n2__)
                    (= smt__CONSTANT__v1__ smt__CONSTANT__v2__)))))
            (forall ((smt__CONSTANT__NI__ Idv))
              (=> (smt__TLA____Mem smt__CONSTANT__NI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__NJ__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__NJ__
                      smt__CONSTANT__Node__)
                    (forall ((smt__CONSTANT__KI__ Idv))
                      (=>
                        (smt__TLA____Mem smt__CONSTANT__KI__
                          smt__CONSTANT__Key__)
                        (forall ((smt__CONSTANT__VALI__ Idv))
                          (=>
                            (smt__TLA____Mem smt__CONSTANT__VALI__
                              smt__CONSTANT__Value__)
                            (or
                              (not
                                (smt__TLA____Mem
                                  (smt__TLA____Tuple__3 smt__CONSTANT__NI__
                                    smt__CONSTANT__KI__ smt__CONSTANT__VALI__)
                                  smt__VARIABLE__transfer__msg__))
                              (not
                                (smt__TLA____Mem smt__CONSTANT__KI__
                                  (smt__TLA____FunApp smt__VARIABLE__owner__
                                    smt__CONSTANT__NJ__))))))))))))
            (forall ((smt__CONSTANT__NJ__ Idv))
              (=> (smt__TLA____Mem smt__CONSTANT__NJ__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__KI__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__KI__ smt__CONSTANT__Key__)
                    (or
                      (smt__TLA____Mem smt__CONSTANT__KI__
                        (smt__TLA____FunApp smt__VARIABLE__owner__
                          smt__CONSTANT__NJ__))
                      (=
                        (smt__TLA____FunApp
                          (smt__TLA____FunApp smt__VARIABLE__table__
                            smt__CONSTANT__NJ__) smt__CONSTANT__KI__)
                        smt__CONSTANT__Nil__))))))
            (forall ((smt__CONSTANT__NI__ Idv))
              (=> (smt__TLA____Mem smt__CONSTANT__NI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__NJ__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__NJ__
                      smt__CONSTANT__Node__)
                    (forall ((smt__CONSTANT__KI__ Idv))
                      (=>
                        (smt__TLA____Mem smt__CONSTANT__KI__
                          smt__CONSTANT__Key__)
                        (or
                          (or
                            (and (= smt__CONSTANT__NI__ smt__CONSTANT__NJ__)
                              (= smt__VARIABLE__owner__
                                smt__VARIABLE__owner__))
                            (not
                              (smt__TLA____Mem smt__CONSTANT__KI__
                                (smt__TLA____FunApp smt__VARIABLE__owner__
                                  smt__CONSTANT__NI__))))
                          (not
                            (smt__TLA____Mem smt__CONSTANT__KI__
                              (smt__TLA____FunApp smt__VARIABLE__owner__
                                smt__CONSTANT__NJ__))))))))))
            (forall ((smt__CONSTANT__NI__ Idv))
              (=> (smt__TLA____Mem smt__CONSTANT__NI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__NJ__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__NJ__
                      smt__CONSTANT__Node__)
                    (forall ((smt__CONSTANT__KI__ Idv))
                      (=>
                        (smt__TLA____Mem smt__CONSTANT__KI__
                          smt__CONSTANT__Key__)
                        (forall ((smt__CONSTANT__VALI__ Idv))
                          (=>
                            (smt__TLA____Mem smt__CONSTANT__VALI__
                              smt__CONSTANT__Value__)
                            (forall ((smt__CONSTANT__VALJ__ Idv))
                              (=>
                                (smt__TLA____Mem smt__CONSTANT__VALJ__
                                  smt__CONSTANT__Value__)
                                (or
                                  (and
                                    (= smt__CONSTANT__NI__
                                      smt__CONSTANT__NJ__)
                                    (= smt__VARIABLE__owner__
                                      smt__VARIABLE__owner__))
                                  (or
                                    (not
                                      (smt__TLA____Mem
                                        (smt__TLA____Tuple__3
                                          smt__CONSTANT__NI__
                                          smt__CONSTANT__KI__
                                          smt__CONSTANT__VALJ__)
                                        smt__VARIABLE__transfer__msg__))
                                    (not
                                      (smt__TLA____Mem
                                        (smt__TLA____Tuple__3
                                          smt__CONSTANT__NJ__
                                          smt__CONSTANT__KI__
                                          smt__CONSTANT__VALI__)
                                        smt__VARIABLE__transfer__msg__))))))))))))))
            (forall ((smt__CONSTANT__NI__ Idv))
              (=> (smt__TLA____Mem smt__CONSTANT__NI__ smt__CONSTANT__Node__)
                (forall ((smt__CONSTANT__KI__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__KI__ smt__CONSTANT__Key__)
                    (forall ((smt__CONSTANT__VALI__ Idv))
                      (=>
                        (smt__TLA____Mem smt__CONSTANT__VALI__
                          smt__CONSTANT__Value__)
                        (forall ((smt__CONSTANT__VALJ__ Idv))
                          (=>
                            (smt__TLA____Mem smt__CONSTANT__VALJ__
                              smt__CONSTANT__Value__)
                            (or
                              (or
                                (and
                                  (= smt__CONSTANT__VALI__
                                    smt__CONSTANT__VALJ__)
                                  (= smt__VARIABLE__owner__
                                    smt__VARIABLE__owner__))
                                (not
                                  (smt__TLA____Mem
                                    (smt__TLA____Tuple__3 smt__CONSTANT__NI__
                                      smt__CONSTANT__KI__
                                      smt__CONSTANT__VALJ__)
                                    smt__VARIABLE__transfer__msg__)))
                              (not
                                (smt__TLA____Mem
                                  (smt__TLA____Tuple__3 smt__CONSTANT__NI__
                                    smt__CONSTANT__KI__ smt__CONSTANT__VALI__)
                                  smt__VARIABLE__transfer__msg__))))))))))))
          (or
            (exists
              ((smt__CONSTANT__k__ Idv) (smt__CONSTANT__v__ Idv)
                (smt__CONSTANT__n__old__ Idv) (smt__CONSTANT__n__new__ Idv))
              (and (smt__TLA____Mem smt__CONSTANT__k__ smt__CONSTANT__Key__)
                (smt__TLA____Mem smt__CONSTANT__v__ smt__CONSTANT__Value__)
                (smt__TLA____Mem smt__CONSTANT__n__old__
                  smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__n__new__
                  smt__CONSTANT__Node__)
                (and
                  (=
                    (smt__TLA____FunApp
                      (smt__TLA____FunApp smt__VARIABLE__table__
                        smt__CONSTANT__n__old__) smt__CONSTANT__k__)
                    smt__CONSTANT__v__)
                  (= smt__VARIABLE__table____prime
                    (smt__TLA____FunExcept smt__VARIABLE__table__
                      smt__CONSTANT__n__old__
                      (smt__TLA____FunExcept
                        (smt__TLA____FunApp smt__VARIABLE__table__
                          smt__CONSTANT__n__old__) smt__CONSTANT__k__
                        smt__CONSTANT__Nil__)))
                  (= smt__VARIABLE__owner____prime
                    (smt__TLA____FunExcept smt__VARIABLE__owner__
                      smt__CONSTANT__n__old__
                      (smt__TLA____SetMinus
                        (smt__TLA____FunApp smt__VARIABLE__owner__
                          smt__CONSTANT__n__old__)
                        (smt__TLA____SetEnum__1 smt__CONSTANT__k__))))
                  (= smt__VARIABLE__transfer__msg____prime
                    (smt__TLA____Cup smt__VARIABLE__transfer__msg__
                      (smt__TLA____SetEnum__1
                        (smt__TLA____Tuple__3 smt__CONSTANT__n__new__
                          smt__CONSTANT__k__ smt__CONSTANT__v__)))))))
            (exists
              ((smt__CONSTANT__n__ Idv) (smt__CONSTANT__k__ Idv)
                (smt__CONSTANT__v__ Idv))
              (and (smt__TLA____Mem smt__CONSTANT__n__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__k__ smt__CONSTANT__Key__)
                (smt__TLA____Mem smt__CONSTANT__v__ smt__CONSTANT__Value__)
                (and
                  (smt__TLA____Mem
                    (smt__TLA____Tuple__3 smt__CONSTANT__n__
                      smt__CONSTANT__k__ smt__CONSTANT__v__)
                    smt__VARIABLE__transfer__msg__)
                  (= smt__VARIABLE__transfer__msg____prime
                    (smt__TLA____SetMinus smt__VARIABLE__transfer__msg__
                      (smt__TLA____SetEnum__1
                        (smt__TLA____Tuple__3 smt__CONSTANT__n__
                          smt__CONSTANT__k__ smt__CONSTANT__v__))))
                  (= smt__VARIABLE__table____prime
                    (smt__TLA____FunExcept smt__VARIABLE__table__
                      smt__CONSTANT__n__
                      (smt__TLA____FunExcept
                        (smt__TLA____FunApp smt__VARIABLE__table__
                          smt__CONSTANT__n__) smt__CONSTANT__k__
                        smt__CONSTANT__v__)))
                  (= smt__VARIABLE__owner____prime
                    (smt__TLA____FunExcept smt__VARIABLE__owner__
                      smt__CONSTANT__n__
                      (smt__TLA____Cup
                        (smt__TLA____FunApp smt__VARIABLE__owner__
                          smt__CONSTANT__n__)
                        (smt__TLA____SetEnum__1 smt__CONSTANT__k__)))))))
            (exists
              ((smt__CONSTANT__n__ Idv) (smt__CONSTANT__k__ Idv)
                (smt__CONSTANT__v__ Idv))
              (and (smt__TLA____Mem smt__CONSTANT__n__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__k__ smt__CONSTANT__Key__)
                (smt__TLA____Mem smt__CONSTANT__v__ smt__CONSTANT__Value__)
                (and
                  (smt__TLA____Mem smt__CONSTANT__k__
                    (smt__TLA____FunApp smt__VARIABLE__owner__
                      smt__CONSTANT__n__))
                  (= smt__VARIABLE__table____prime
                    (smt__TLA____FunExcept smt__VARIABLE__table__
                      smt__CONSTANT__n__
                      (smt__TLA____FunExcept
                        (smt__TLA____FunApp smt__VARIABLE__table__
                          smt__CONSTANT__n__) smt__CONSTANT__k__
                        smt__CONSTANT__v__)))
                  (and
                    (= smt__VARIABLE__owner____prime smt__VARIABLE__owner__)
                    (= smt__VARIABLE__transfer__msg____prime
                      smt__VARIABLE__transfer__msg__)))))))
        (and
          (and
            (smt__TLA____Mem smt__VARIABLE__table____prime
              (smt__TLA____FunSet smt__CONSTANT__Node__
                (smt__TLA____FunSet smt__CONSTANT__Key__
                  (smt__TLA____Cup smt__CONSTANT__Value__
                    (smt__TLA____SetEnum__1 smt__CONSTANT__Nil__)))))
            (smt__TLA____Mem smt__VARIABLE__owner____prime
              (smt__TLA____FunSet smt__CONSTANT__Node__
                (smt__TLA____Subset smt__CONSTANT__Key__)))
            (smt__TLA____Mem smt__VARIABLE__transfer__msg____prime
              (smt__TLA____Subset
                (smt__TLA____Product__3 smt__CONSTANT__Node__
                  smt__CONSTANT__Key__ smt__CONSTANT__Value__))))
          (forall
            ((smt__CONSTANT__n1__ Idv) (smt__CONSTANT__n2__ Idv)
              (smt__CONSTANT__k__ Idv) (smt__CONSTANT__v1__ Idv)
              (smt__CONSTANT__v2__ Idv))
            (=>
              (and
                (smt__TLA____Mem smt__CONSTANT__n1__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__n2__ smt__CONSTANT__Node__)
                (smt__TLA____Mem smt__CONSTANT__k__ smt__CONSTANT__Key__)
                (smt__TLA____Mem smt__CONSTANT__v1__ smt__CONSTANT__Value__)
                (smt__TLA____Mem smt__CONSTANT__v2__ smt__CONSTANT__Value__))
              (=>
                (and
                  (=
                    (smt__TLA____FunApp
                      (smt__TLA____FunApp smt__VARIABLE__table____prime
                        smt__CONSTANT__n1__) smt__CONSTANT__k__)
                    smt__CONSTANT__v1__)
                  (=
                    (smt__TLA____FunApp
                      (smt__TLA____FunApp smt__VARIABLE__table____prime
                        smt__CONSTANT__n2__) smt__CONSTANT__k__)
                    smt__CONSTANT__v2__))
                (and (= smt__CONSTANT__n1__ smt__CONSTANT__n2__)
                  (= smt__CONSTANT__v1__ smt__CONSTANT__v2__)))))
          (forall ((smt__CONSTANT__NI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__NI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__NJ__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__NJ__ smt__CONSTANT__Node__)
                  (forall ((smt__CONSTANT__KI__ Idv))
                    (=>
                      (smt__TLA____Mem smt__CONSTANT__KI__
                        smt__CONSTANT__Key__)
                      (forall ((smt__CONSTANT__VALI__ Idv))
                        (=>
                          (smt__TLA____Mem smt__CONSTANT__VALI__
                            smt__CONSTANT__Value__)
                          (or
                            (not
                              (smt__TLA____Mem
                                (smt__TLA____Tuple__3 smt__CONSTANT__NI__
                                  smt__CONSTANT__KI__ smt__CONSTANT__VALI__)
                                smt__VARIABLE__transfer__msg____prime))
                            (not
                              (smt__TLA____Mem smt__CONSTANT__KI__
                                (smt__TLA____FunApp
                                  smt__VARIABLE__owner____prime
                                  smt__CONSTANT__NJ__))))))))))))
          (forall ((smt__CONSTANT__NJ__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__NJ__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__KI__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__KI__ smt__CONSTANT__Key__)
                  (or
                    (smt__TLA____Mem smt__CONSTANT__KI__
                      (smt__TLA____FunApp smt__VARIABLE__owner____prime
                        smt__CONSTANT__NJ__))
                    (=
                      (smt__TLA____FunApp
                        (smt__TLA____FunApp smt__VARIABLE__table____prime
                          smt__CONSTANT__NJ__) smt__CONSTANT__KI__)
                      smt__CONSTANT__Nil__))))))
          (forall ((smt__CONSTANT__NI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__NI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__NJ__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__NJ__ smt__CONSTANT__Node__)
                  (forall ((smt__CONSTANT__KI__ Idv))
                    (=>
                      (smt__TLA____Mem smt__CONSTANT__KI__
                        smt__CONSTANT__Key__)
                      (or
                        (or
                          (and (= smt__CONSTANT__NI__ smt__CONSTANT__NJ__)
                            (= smt__VARIABLE__owner____prime
                              smt__VARIABLE__owner____prime))
                          (not
                            (smt__TLA____Mem smt__CONSTANT__KI__
                              (smt__TLA____FunApp
                                smt__VARIABLE__owner____prime
                                smt__CONSTANT__NI__))))
                        (not
                          (smt__TLA____Mem smt__CONSTANT__KI__
                            (smt__TLA____FunApp smt__VARIABLE__owner____prime
                              smt__CONSTANT__NJ__))))))))))
          (forall ((smt__CONSTANT__NI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__NI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__NJ__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__NJ__ smt__CONSTANT__Node__)
                  (forall ((smt__CONSTANT__KI__ Idv))
                    (=>
                      (smt__TLA____Mem smt__CONSTANT__KI__
                        smt__CONSTANT__Key__)
                      (forall ((smt__CONSTANT__VALI__ Idv))
                        (=>
                          (smt__TLA____Mem smt__CONSTANT__VALI__
                            smt__CONSTANT__Value__)
                          (forall ((smt__CONSTANT__VALJ__ Idv))
                            (=>
                              (smt__TLA____Mem smt__CONSTANT__VALJ__
                                smt__CONSTANT__Value__)
                              (or
                                (and
                                  (= smt__CONSTANT__NI__ smt__CONSTANT__NJ__)
                                  (= smt__VARIABLE__owner____prime
                                    smt__VARIABLE__owner____prime))
                                (or
                                  (not
                                    (smt__TLA____Mem
                                      (smt__TLA____Tuple__3
                                        smt__CONSTANT__NI__
                                        smt__CONSTANT__KI__
                                        smt__CONSTANT__VALJ__)
                                      smt__VARIABLE__transfer__msg____prime))
                                  (not
                                    (smt__TLA____Mem
                                      (smt__TLA____Tuple__3
                                        smt__CONSTANT__NJ__
                                        smt__CONSTANT__KI__
                                        smt__CONSTANT__VALI__)
                                      smt__VARIABLE__transfer__msg____prime))))))))))))))
          (forall ((smt__CONSTANT__NI__ Idv))
            (=> (smt__TLA____Mem smt__CONSTANT__NI__ smt__CONSTANT__Node__)
              (forall ((smt__CONSTANT__KI__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__KI__ smt__CONSTANT__Key__)
                  (forall ((smt__CONSTANT__VALI__ Idv))
                    (=>
                      (smt__TLA____Mem smt__CONSTANT__VALI__
                        smt__CONSTANT__Value__)
                      (forall ((smt__CONSTANT__VALJ__ Idv))
                        (=>
                          (smt__TLA____Mem smt__CONSTANT__VALJ__
                            smt__CONSTANT__Value__)
                          (or
                            (or
                              (and
                                (= smt__CONSTANT__VALI__
                                  smt__CONSTANT__VALJ__)
                                (= smt__VARIABLE__owner____prime
                                  smt__VARIABLE__owner____prime))
                              (not
                                (smt__TLA____Mem
                                  (smt__TLA____Tuple__3 smt__CONSTANT__NI__
                                    smt__CONSTANT__KI__ smt__CONSTANT__VALJ__)
                                  smt__VARIABLE__transfer__msg____prime)))
                            (not
                              (smt__TLA____Mem
                                (smt__TLA____Tuple__3 smt__CONSTANT__NI__
                                  smt__CONSTANT__KI__ smt__CONSTANT__VALI__)
                                smt__VARIABLE__transfer__msg____prime))))))))))))))
    :named |Goal|))

(check-sat)
(exit)
