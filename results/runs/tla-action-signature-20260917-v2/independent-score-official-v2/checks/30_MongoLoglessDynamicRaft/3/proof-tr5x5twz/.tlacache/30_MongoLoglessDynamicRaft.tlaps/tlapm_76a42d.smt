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
;;	       NEW CONSTANT CONSTANT_MaxConfigVersion_
;;	PROVE  (/\ /\ VARIABLE_currentTerm_ \in [CONSTANT_Server_ -> Nat]
;;	           /\ VARIABLE_state_
;;	              \in [CONSTANT_Server_ ->
;;	                     {CONSTANT_Secondary_, CONSTANT_Primary_}]
;;	           /\ VARIABLE_config_
;;	              \in [CONSTANT_Server_ -> SUBSET CONSTANT_Server_]
;;	           /\ VARIABLE_configVersion_ \in [CONSTANT_Server_ -> Nat]
;;	           /\ VARIABLE_configTerm_ \in [CONSTANT_Server_ -> Nat]
;;	        /\ /\ \A CONSTANT_s_, CONSTANT_t_ \in CONSTANT_Server_ :
;;	                 (/\ VARIABLE_state_[CONSTANT_s_] = CONSTANT_Primary_
;;	                  /\ VARIABLE_state_[CONSTANT_t_] = CONSTANT_Primary_
;;	                  /\ VARIABLE_currentTerm_[CONSTANT_s_]
;;	                     = VARIABLE_currentTerm_[CONSTANT_t_])
;;	                 => CONSTANT_s_ = CONSTANT_t_
;;	        /\ \A CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Server_ :
;;	              (\A CONSTANT_qx_
;;	                  \in {CONSTANT_i__1 \in SUBSET VARIABLE_config_[CONSTANT_i_] :
;;	                         CONSTANT_Cardinality_(CONSTANT_i__1) * 2
;;	                         > CONSTANT_Cardinality_(VARIABLE_config_[CONSTANT_i_])},
;;	                  CONSTANT_qy_
;;	                  \in {CONSTANT_i__1 \in SUBSET VARIABLE_config_[CONSTANT_j_] :
;;	                         CONSTANT_Cardinality_(CONSTANT_i__1) * 2
;;	                         > CONSTANT_Cardinality_(VARIABLE_config_[CONSTANT_j_])} :
;;	                  CONSTANT_qx_ \cap CONSTANT_qy_ # {})
;;	              \/ ((\A CONSTANT_Q_
;;	                      \in {CONSTANT_i__1 \in
;;	                             SUBSET VARIABLE_config_[CONSTANT_i_] :
;;	                             CONSTANT_Cardinality_(CONSTANT_i__1) * 2
;;	                             > CONSTANT_Cardinality_(VARIABLE_config_[CONSTANT_i_])} :
;;	                      \E CONSTANT_n_ \in CONSTANT_Q_ :
;;	                         \/ <<VARIABLE_configVersion_[CONSTANT_n_],
;;	                              VARIABLE_configTerm_[CONSTANT_n_]>>[2]
;;	                            > <<VARIABLE_configVersion_[CONSTANT_i_],
;;	                                VARIABLE_configTerm_[CONSTANT_i_]>>[2]
;;	                         \/ /\ <<VARIABLE_configVersion_[CONSTANT_n_],
;;	                                 VARIABLE_configTerm_[CONSTANT_n_]>>[2]
;;	                               = <<VARIABLE_configVersion_[CONSTANT_i_],
;;	                                   VARIABLE_configTerm_[CONSTANT_i_]>>[2]
;;	                            /\ <<VARIABLE_configVersion_[CONSTANT_n_],
;;	                                 VARIABLE_configTerm_[CONSTANT_n_]>>[1]
;;	                               > <<VARIABLE_configVersion_[CONSTANT_i_],
;;	                                   VARIABLE_configTerm_[CONSTANT_i_]>>[1])
;;	                  \/ ((\A CONSTANT_Q_
;;	                          \in {CONSTANT_i__1 \in
;;	                                 SUBSET VARIABLE_config_[CONSTANT_j_] :
;;	                                 CONSTANT_Cardinality_(CONSTANT_i__1) * 2
;;	                                 > CONSTANT_Cardinality_(VARIABLE_config_[CONSTANT_j_])} :
;;	                          \E CONSTANT_n_ \in CONSTANT_Q_ :
;;	                             \/ <<VARIABLE_configVersion_[CONSTANT_n_],
;;	                                  VARIABLE_configTerm_[CONSTANT_n_]>>[2]
;;	                                > <<VARIABLE_configVersion_[CONSTANT_j_],
;;	                                    VARIABLE_configTerm_[CONSTANT_j_]>>[2]
;;	                             \/ /\ <<VARIABLE_configVersion_[CONSTANT_n_],
;;	                                     VARIABLE_configTerm_[CONSTANT_n_]>>[2]
;;	                                   = <<VARIABLE_configVersion_[CONSTANT_j_],
;;	                                       VARIABLE_configTerm_[CONSTANT_j_]>>[2]
;;	                                /\ <<VARIABLE_configVersion_[CONSTANT_n_],
;;	                                     VARIABLE_configTerm_[CONSTANT_n_]>>[1]
;;	                                   > <<VARIABLE_configVersion_[CONSTANT_j_],
;;	                                       VARIABLE_configTerm_[CONSTANT_j_]>>[1])
;;	                      /\ TRUE))
;;	        /\ \A CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Server_ :
;;	              VARIABLE_config_[CONSTANT_i_] = VARIABLE_config_[CONSTANT_j_]
;;	              \/ ((\/ VARIABLE_configTerm_[CONSTANT_j_]
;;	                      > VARIABLE_configTerm_[CONSTANT_i_]
;;	                   \/ /\ VARIABLE_configTerm_[CONSTANT_j_]
;;	                         = VARIABLE_configTerm_[CONSTANT_i_]
;;	                      /\ VARIABLE_configVersion_[CONSTANT_j_]
;;	                         > VARIABLE_configVersion_[CONSTANT_i_])
;;	                  \/ ((\/ VARIABLE_configTerm_[CONSTANT_i_]
;;	                          > VARIABLE_configTerm_[CONSTANT_j_]
;;	                       \/ /\ VARIABLE_configTerm_[CONSTANT_i_]
;;	                             = VARIABLE_configTerm_[CONSTANT_j_]
;;	                          /\ VARIABLE_configVersion_[CONSTANT_i_]
;;	                             > VARIABLE_configVersion_[CONSTANT_j_])
;;	                      /\ TRUE))
;;	        /\ \A CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Server_ :
;;	              ~VARIABLE_configTerm_[CONSTANT_i_]
;;	               = VARIABLE_configTerm_[CONSTANT_j_]
;;	              \/ (~VARIABLE_state_[CONSTANT_i_] = CONSTANT_Primary_
;;	                  \/ (~(\/ VARIABLE_configTerm_[CONSTANT_j_]
;;	                           > VARIABLE_configTerm_[CONSTANT_i_]
;;	                        \/ /\ VARIABLE_configTerm_[CONSTANT_j_]
;;	                              = VARIABLE_configTerm_[CONSTANT_i_]
;;	                           /\ VARIABLE_configVersion_[CONSTANT_j_]
;;	                              > VARIABLE_configVersion_[CONSTANT_i_])
;;	                      /\ TRUE))
;;	        /\ \A CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Server_ :
;;	              \A CONSTANT_Q_
;;	                 \in {CONSTANT_i__1 \in SUBSET VARIABLE_config_[CONSTANT_j_] :
;;	                        CONSTANT_Cardinality_(CONSTANT_i__1) * 2
;;	                        > CONSTANT_Cardinality_(VARIABLE_config_[CONSTANT_j_])} :
;;	                 \E CONSTANT_n_ \in CONSTANT_Q_ :
;;	                    VARIABLE_currentTerm_[CONSTANT_n_]
;;	                    >= VARIABLE_configTerm_[CONSTANT_i_]
;;	                    \/ (\A CONSTANT_Q__1
;;	                           \in {CONSTANT_i__1 \in
;;	                                  SUBSET VARIABLE_config_[CONSTANT_j_] :
;;	                                  CONSTANT_Cardinality_(CONSTANT_i__1) * 2
;;	                                  > CONSTANT_Cardinality_(VARIABLE_config_[CONSTANT_j_])} :
;;	                           \E CONSTANT_n__1 \in CONSTANT_Q__1 :
;;	                              \/ <<VARIABLE_configVersion_[CONSTANT_n__1],
;;	                                   VARIABLE_configTerm_[CONSTANT_n__1]>>[2]
;;	                                 > <<VARIABLE_configVersion_[CONSTANT_j_],
;;	                                     VARIABLE_configTerm_[CONSTANT_j_]>>[2]
;;	                              \/ /\ <<VARIABLE_configVersion_[CONSTANT_n__1],
;;	                                      VARIABLE_configTerm_[CONSTANT_n__1]>>[2]
;;	                                    = <<VARIABLE_configVersion_[CONSTANT_j_],
;;	                                        VARIABLE_configTerm_[CONSTANT_j_]>>[2]
;;	                                 /\ <<VARIABLE_configVersion_[CONSTANT_n__1],
;;	                                      VARIABLE_configTerm_[CONSTANT_n__1]>>[1]
;;	                                    > <<VARIABLE_configVersion_[CONSTANT_j_],
;;	                                        VARIABLE_configTerm_[CONSTANT_j_]>>[1])
;;	        /\ \A CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Server_ :
;;	              VARIABLE_configTerm_[CONSTANT_j_]
;;	              = VARIABLE_currentTerm_[CONSTANT_j_]
;;	              \/ (~VARIABLE_state_[CONSTANT_j_] = CONSTANT_Primary_ /\ TRUE))
;;	       /\ (\/ \E CONSTANT_s_ \in CONSTANT_Server_,
;;	                 CONSTANT_newConfig_ \in SUBSET CONSTANT_Server_ :
;;	                 /\ VARIABLE_state_[CONSTANT_s_] = CONSTANT_Primary_
;;	                 /\ /\ VARIABLE_state_[CONSTANT_s_] = CONSTANT_Primary_
;;	                    /\ VARIABLE_configTerm_[CONSTANT_s_]
;;	                       = VARIABLE_currentTerm_[CONSTANT_s_]
;;	                    /\ \E CONSTANT_Q_
;;	                          \in {CONSTANT_i_ \in
;;	                                 SUBSET VARIABLE_config_[CONSTANT_s_] :
;;	                                 CONSTANT_Cardinality_(CONSTANT_i_) * 2
;;	                                 > CONSTANT_Cardinality_(VARIABLE_config_[CONSTANT_s_])} :
;;	                          \A CONSTANT_t_ \in CONSTANT_Q_ :
;;	                             /\ VARIABLE_configVersion_[CONSTANT_s_]
;;	                                = VARIABLE_configVersion_[CONSTANT_t_]
;;	                             /\ VARIABLE_configTerm_[CONSTANT_s_]
;;	                                = VARIABLE_configTerm_[CONSTANT_t_]
;;	                             /\ VARIABLE_currentTerm_[CONSTANT_t_]
;;	                                = VARIABLE_currentTerm_[CONSTANT_s_]
;;	                 /\ \A CONSTANT_qx_
;;	                       \in {CONSTANT_i_ \in
;;	                              SUBSET VARIABLE_config_[CONSTANT_s_] :
;;	                              CONSTANT_Cardinality_(CONSTANT_i_) * 2
;;	                              > CONSTANT_Cardinality_(VARIABLE_config_[CONSTANT_s_])},
;;	                       CONSTANT_qy_
;;	                       \in {CONSTANT_i_ \in SUBSET CONSTANT_newConfig_ :
;;	                              CONSTANT_Cardinality_(CONSTANT_i_) * 2
;;	                              > CONSTANT_Cardinality_(CONSTANT_newConfig_)} :
;;	                       CONSTANT_qx_ \cap CONSTANT_qy_ # {}
;;	                 /\ CONSTANT_s_ \in CONSTANT_newConfig_
;;	                 /\ ?VARIABLE_configTerm_#prime
;;	                    = [VARIABLE_configTerm_ EXCEPT
;;	                         ![CONSTANT_s_] = VARIABLE_currentTerm_[CONSTANT_s_]]
;;	                 /\ ?VARIABLE_configVersion_#prime
;;	                    = [VARIABLE_configVersion_ EXCEPT
;;	                         ![CONSTANT_s_] = VARIABLE_configVersion_[CONSTANT_s_]
;;	                                          + 1]
;;	                 /\ ?VARIABLE_config_#prime
;;	                    = [VARIABLE_config_ EXCEPT
;;	                         ![CONSTANT_s_] = CONSTANT_newConfig_]
;;	                 /\ /\ ?VARIABLE_currentTerm_#prime = VARIABLE_currentTerm_
;;	                    /\ ?VARIABLE_state_#prime = VARIABLE_state_
;;	           \/ \E CONSTANT_s_, CONSTANT_t_ \in CONSTANT_Server_ :
;;	                 /\ VARIABLE_state_[CONSTANT_t_] = CONSTANT_Secondary_
;;	                 /\ \/ VARIABLE_configTerm_[CONSTANT_s_]
;;	                       > VARIABLE_configTerm_[CONSTANT_t_]
;;	                    \/ /\ VARIABLE_configTerm_[CONSTANT_s_]
;;	                          = VARIABLE_configTerm_[CONSTANT_t_]
;;	                       /\ VARIABLE_configVersion_[CONSTANT_s_]
;;	                          > VARIABLE_configVersion_[CONSTANT_t_]
;;	                 /\ ?VARIABLE_configVersion_#prime
;;	                    = [VARIABLE_configVersion_ EXCEPT
;;	                         ![CONSTANT_t_] = VARIABLE_configVersion_[CONSTANT_s_]]
;;	                 /\ ?VARIABLE_configTerm_#prime
;;	                    = [VARIABLE_configTerm_ EXCEPT
;;	                         ![CONSTANT_t_] = VARIABLE_configTerm_[CONSTANT_s_]]
;;	                 /\ ?VARIABLE_config_#prime
;;	                    = [VARIABLE_config_ EXCEPT
;;	                         ![CONSTANT_t_] = VARIABLE_config_[CONSTANT_s_]]
;;	                 /\ /\ ?VARIABLE_currentTerm_#prime = VARIABLE_currentTerm_
;;	                    /\ ?VARIABLE_state_#prime = VARIABLE_state_
;;	           \/ \E CONSTANT_i_ \in CONSTANT_Server_ :
;;	                 \E CONSTANT_Q_
;;	                    \in {CONSTANT_i__1 \in
;;	                           SUBSET VARIABLE_config_[CONSTANT_i_] :
;;	                           CONSTANT_Cardinality_(CONSTANT_i__1) * 2
;;	                           > CONSTANT_Cardinality_(VARIABLE_config_[CONSTANT_i_])} :
;;	                    /\ CONSTANT_i_ \in VARIABLE_config_[CONSTANT_i_]
;;	                    /\ CONSTANT_i_ \in CONSTANT_Q_
;;	                    /\ \A CONSTANT_v_ \in CONSTANT_Q_ :
;;	                          /\ VARIABLE_currentTerm_[CONSTANT_v_]
;;	                             < VARIABLE_currentTerm_[CONSTANT_i_] + 1
;;	                          /\ \/ /\ VARIABLE_configTerm_[CONSTANT_i_]
;;	                                   = VARIABLE_configTerm_[CONSTANT_v_]
;;	                                /\ VARIABLE_configVersion_[CONSTANT_i_]
;;	                                   = VARIABLE_configVersion_[CONSTANT_v_]
;;	                             \/ \/ VARIABLE_configTerm_[CONSTANT_i_]
;;	                                   > VARIABLE_configTerm_[CONSTANT_v_]
;;	                                \/ /\ VARIABLE_configTerm_[CONSTANT_i_]
;;	                                      = VARIABLE_configTerm_[CONSTANT_v_]
;;	                                   /\ VARIABLE_configVersion_[CONSTANT_i_]
;;	                                      > VARIABLE_configVersion_[CONSTANT_v_]
;;	                    /\ ?VARIABLE_currentTerm_#prime
;;	                       = [CONSTANT_s_ \in CONSTANT_Server_ |->
;;	                            IF CONSTANT_s_ \in CONSTANT_Q_
;;	                              THEN VARIABLE_currentTerm_[CONSTANT_i_] + 1
;;	                              ELSE VARIABLE_currentTerm_[CONSTANT_s_]]
;;	                    /\ ?VARIABLE_state_#prime
;;	                       = [CONSTANT_s_ \in CONSTANT_Server_ |->
;;	                            IF CONSTANT_s_ = CONSTANT_i_
;;	                              THEN CONSTANT_Primary_
;;	                              ELSE IF CONSTANT_s_ \in CONSTANT_Q_
;;	                                     THEN CONSTANT_Secondary_
;;	                                     ELSE VARIABLE_state_[CONSTANT_s_]]
;;	                    /\ ?VARIABLE_configTerm_#prime
;;	                       = [VARIABLE_configTerm_ EXCEPT
;;	                            ![CONSTANT_i_] = VARIABLE_currentTerm_[CONSTANT_i_]
;;	                                             + 1]
;;	                    /\ /\ ?VARIABLE_config_#prime = VARIABLE_config_
;;	                       /\ ?VARIABLE_configVersion_#prime
;;	                          = VARIABLE_configVersion_
;;	           \/ \E CONSTANT_s_, CONSTANT_t_ \in CONSTANT_Server_ :
;;	                 /\ /\ VARIABLE_currentTerm_[CONSTANT_s_]
;;	                       > VARIABLE_currentTerm_[CONSTANT_t_]
;;	                    /\ ?VARIABLE_currentTerm_#prime
;;	                       = [VARIABLE_currentTerm_ EXCEPT
;;	                            ![CONSTANT_t_] = VARIABLE_currentTerm_[CONSTANT_s_]]
;;	                    /\ ?VARIABLE_state_#prime
;;	                       = [VARIABLE_state_ EXCEPT
;;	                            ![CONSTANT_t_] = CONSTANT_Secondary_]
;;	                 /\ /\ ?VARIABLE_configVersion_#prime
;;	                       = VARIABLE_configVersion_
;;	                    /\ ?VARIABLE_configTerm_#prime = VARIABLE_configTerm_
;;	                    /\ ?VARIABLE_config_#prime = VARIABLE_config_)
;;	       => (/\ /\ ?VARIABLE_currentTerm_#prime \in [CONSTANT_Server_ -> Nat]
;;	              /\ ?VARIABLE_state_#prime
;;	                 \in [CONSTANT_Server_ ->
;;	                        {CONSTANT_Secondary_, CONSTANT_Primary_}]
;;	              /\ ?VARIABLE_config_#prime
;;	                 \in [CONSTANT_Server_ -> SUBSET CONSTANT_Server_]
;;	              /\ ?VARIABLE_configVersion_#prime \in [CONSTANT_Server_ -> Nat]
;;	              /\ ?VARIABLE_configTerm_#prime \in [CONSTANT_Server_ -> Nat]
;;	           /\ /\ \A CONSTANT_s_, CONSTANT_t_ \in CONSTANT_Server_ :
;;	                    (/\ ?VARIABLE_state_#prime[CONSTANT_s_]
;;	                        = CONSTANT_Primary_
;;	                     /\ ?VARIABLE_state_#prime[CONSTANT_t_]
;;	                        = CONSTANT_Primary_
;;	                     /\ ?VARIABLE_currentTerm_#prime[CONSTANT_s_]
;;	                        = ?VARIABLE_currentTerm_#prime[CONSTANT_t_])
;;	                    => CONSTANT_s_ = CONSTANT_t_
;;	           /\ \A CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Server_ :
;;	                 (\A CONSTANT_qx_
;;	                     \in {CONSTANT_i__1 \in
;;	                            SUBSET ?VARIABLE_config_#prime[CONSTANT_i_] :
;;	                            CONSTANT_Cardinality_(CONSTANT_i__1) * 2
;;	                            > CONSTANT_Cardinality_(?VARIABLE_config_#prime[CONSTANT_i_])},
;;	                     CONSTANT_qy_
;;	                     \in {CONSTANT_i__1 \in
;;	                            SUBSET ?VARIABLE_config_#prime[CONSTANT_j_] :
;;	                            CONSTANT_Cardinality_(CONSTANT_i__1) * 2
;;	                            > CONSTANT_Cardinality_(?VARIABLE_config_#prime[CONSTANT_j_])} :
;;	                     CONSTANT_qx_ \cap CONSTANT_qy_ # {})
;;	                 \/ ((\A CONSTANT_Q_
;;	                         \in {CONSTANT_i__1 \in
;;	                                SUBSET ?VARIABLE_config_#prime[CONSTANT_i_] :
;;	                                CONSTANT_Cardinality_(CONSTANT_i__1) * 2
;;	                                > CONSTANT_Cardinality_(?VARIABLE_config_#prime[CONSTANT_i_])} :
;;	                         \E CONSTANT_n_ \in CONSTANT_Q_ :
;;	                            \/ <<?VARIABLE_configVersion_#prime[CONSTANT_n_],
;;	                                 ?VARIABLE_configTerm_#prime[CONSTANT_n_]>>[2]
;;	                               > <<?VARIABLE_configVersion_#prime[CONSTANT_i_],
;;	                                   ?VARIABLE_configTerm_#prime[CONSTANT_i_]>>[2]
;;	                            \/ /\ <<?VARIABLE_configVersion_#prime[CONSTANT_n_],
;;	                                    ?VARIABLE_configTerm_#prime[CONSTANT_n_]>>[2]
;;	                                  = <<?VARIABLE_configVersion_#prime[CONSTANT_i_],
;;	                                      ?VARIABLE_configTerm_#prime[CONSTANT_i_]>>[2]
;;	                               /\ <<?VARIABLE_configVersion_#prime[CONSTANT_n_],
;;	                                    ?VARIABLE_configTerm_#prime[CONSTANT_n_]>>[1]
;;	                                  > <<?VARIABLE_configVersion_#prime[CONSTANT_i_],
;;	                                      ?VARIABLE_configTerm_#prime[CONSTANT_i_]>>[1])
;;	                     \/ ((\A CONSTANT_Q_
;;	                             \in {CONSTANT_i__1 \in
;;	                                    SUBSET ?VARIABLE_config_#prime[CONSTANT_j_] :
;;	                                    CONSTANT_Cardinality_(CONSTANT_i__1) * 2
;;	                                    > CONSTANT_Cardinality_(?VARIABLE_config_#prime[CONSTANT_j_])} :
;;	                             \E CONSTANT_n_ \in CONSTANT_Q_ :
;;	                                \/ <<?VARIABLE_configVersion_#prime[CONSTANT_n_],
;;	                                     ?VARIABLE_configTerm_#prime[CONSTANT_n_]>>[2]
;;	                                   > <<?VARIABLE_configVersion_#prime[CONSTANT_j_],
;;	                                       ?VARIABLE_configTerm_#prime[CONSTANT_j_]>>[2]
;;	                                \/ /\ <<?VARIABLE_configVersion_#prime[CONSTANT_n_],
;;	                                        ?VARIABLE_configTerm_#prime[CONSTANT_n_]>>[2]
;;	                                      = <<?VARIABLE_configVersion_#prime[CONSTANT_j_],
;;	                                          ?VARIABLE_configTerm_#prime[CONSTANT_j_]>>[2]
;;	                                   /\ <<?VARIABLE_configVersion_#prime[CONSTANT_n_],
;;	                                        ?VARIABLE_configTerm_#prime[CONSTANT_n_]>>[1]
;;	                                      > <<?VARIABLE_configVersion_#prime[CONSTANT_j_],
;;	                                          ?VARIABLE_configTerm_#prime[CONSTANT_j_]>>[1])
;;	                         /\ TRUE))
;;	           /\ \A CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Server_ :
;;	                 ?VARIABLE_config_#prime[CONSTANT_i_]
;;	                 = ?VARIABLE_config_#prime[CONSTANT_j_]
;;	                 \/ ((\/ ?VARIABLE_configTerm_#prime[CONSTANT_j_]
;;	                         > ?VARIABLE_configTerm_#prime[CONSTANT_i_]
;;	                      \/ /\ ?VARIABLE_configTerm_#prime[CONSTANT_j_]
;;	                            = ?VARIABLE_configTerm_#prime[CONSTANT_i_]
;;	                         /\ ?VARIABLE_configVersion_#prime[CONSTANT_j_]
;;	                            > ?VARIABLE_configVersion_#prime[CONSTANT_i_])
;;	                     \/ ((\/ ?VARIABLE_configTerm_#prime[CONSTANT_i_]
;;	                             > ?VARIABLE_configTerm_#prime[CONSTANT_j_]
;;	                          \/ /\ ?VARIABLE_configTerm_#prime[CONSTANT_i_]
;;	                                = ?VARIABLE_configTerm_#prime[CONSTANT_j_]
;;	                             /\ ?VARIABLE_configVersion_#prime[CONSTANT_i_]
;;	                                > ?VARIABLE_configVersion_#prime[CONSTANT_j_])
;;	                         /\ TRUE))
;;	           /\ \A CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Server_ :
;;	                 ~?VARIABLE_configTerm_#prime[CONSTANT_i_]
;;	                  = ?VARIABLE_configTerm_#prime[CONSTANT_j_]
;;	                 \/ (~?VARIABLE_state_#prime[CONSTANT_i_] = CONSTANT_Primary_
;;	                     \/ (~(\/ ?VARIABLE_configTerm_#prime[CONSTANT_j_]
;;	                              > ?VARIABLE_configTerm_#prime[CONSTANT_i_]
;;	                           \/ /\ ?VARIABLE_configTerm_#prime[CONSTANT_j_]
;;	                                 = ?VARIABLE_configTerm_#prime[CONSTANT_i_]
;;	                              /\ ?VARIABLE_configVersion_#prime[CONSTANT_j_]
;;	                                 > ?VARIABLE_configVersion_#prime[CONSTANT_i_])
;;	                         /\ TRUE))
;;	           /\ \A CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Server_ :
;;	                 \A CONSTANT_Q_
;;	                    \in {CONSTANT_i__1 \in
;;	                           SUBSET ?VARIABLE_config_#prime[CONSTANT_j_] :
;;	                           CONSTANT_Cardinality_(CONSTANT_i__1) * 2
;;	                           > CONSTANT_Cardinality_(?VARIABLE_config_#prime[CONSTANT_j_])} :
;;	                    \E CONSTANT_n_ \in CONSTANT_Q_ :
;;	                       ?VARIABLE_currentTerm_#prime[CONSTANT_n_]
;;	                       >= ?VARIABLE_configTerm_#prime[CONSTANT_i_]
;;	                       \/ (\A CONSTANT_Q__1
;;	                              \in {CONSTANT_i__1 \in
;;	                                     SUBSET ?VARIABLE_config_#prime[CONSTANT_j_] :
;;	                                     CONSTANT_Cardinality_(CONSTANT_i__1) * 2
;;	                                     > CONSTANT_Cardinality_(?VARIABLE_config_#prime[CONSTANT_j_])} :
;;	                              \E CONSTANT_n__1 \in CONSTANT_Q__1 :
;;	                                 \/ <<?VARIABLE_configVersion_#prime[CONSTANT_n__1],
;;	                                      ?VARIABLE_configTerm_#prime[CONSTANT_n__1]>>[2]
;;	                                    > <<?VARIABLE_configVersion_#prime[CONSTANT_j_],
;;	                                        ?VARIABLE_configTerm_#prime[CONSTANT_j_]>>[2]
;;	                                 \/ /\ <<?VARIABLE_configVersion_#prime[CONSTANT_n__1],
;;	                                         ?VARIABLE_configTerm_#prime[CONSTANT_n__1]>>[2]
;;	                                       = <<?VARIABLE_configVersion_#prime[CONSTANT_j_],
;;	                                           ?VARIABLE_configTerm_#prime[CONSTANT_j_]>>[2]
;;	                                    /\ <<?VARIABLE_configVersion_#prime[CONSTANT_n__1],
;;	                                         ?VARIABLE_configTerm_#prime[CONSTANT_n__1]>>[1]
;;	                                       > <<?VARIABLE_configVersion_#prime[CONSTANT_j_],
;;	                                           ?VARIABLE_configTerm_#prime[CONSTANT_j_]>>[1])
;;	           /\ \A CONSTANT_i_, CONSTANT_j_ \in CONSTANT_Server_ :
;;	                 ?VARIABLE_configTerm_#prime[CONSTANT_j_]
;;	                 = ?VARIABLE_currentTerm_#prime[CONSTANT_j_]
;;	                 \/ (~?VARIABLE_state_#prime[CONSTANT_j_] = CONSTANT_Primary_
;;	                     /\ TRUE))
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./30_MongoLoglessDynamicRaft.tla", line 248, characters 1-2

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Cap (Idv Idv) Idv)

(declare-fun smt__TLA____Cast__Int (Int) Idv)

(declare-fun smt__TLA____FunApp (Idv Idv) Idv)

(declare-fun smt__TLA____FunDom (Idv) Idv)

(declare-fun smt__TLA____FunExcept (Idv Idv Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA____FunIsafcn (Idv) Bool)

(declare-fun smt__TLA____FunSet (Idv Idv) Idv)

(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)

(declare-fun smt__TLA____IntPlus (Idv Idv) Idv)

(declare-fun smt__TLA____IntRange (Idv Idv) Idv)

(declare-fun smt__TLA____IntSet () Idv)

(declare-fun smt__TLA____IntTimes (Idv Idv) Idv)

(declare-fun smt__TLA____Len (Idv) Idv)

(declare-fun smt__TLA____Mem (Idv Idv) Bool)

(declare-fun smt__TLA____NatSet () Idv)

(declare-fun smt__TLA____Proj__Int (Idv) Int)

(declare-fun smt__TLA____Seq (Idv) Idv)

(declare-fun smt__TLA____SetEnum__0 () Idv)

(declare-fun smt__TLA____SetEnum__2 (Idv Idv) Idv)

(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)

; omitted declaration of 'TLA__SetSt' (second-order)

(declare-fun smt__TLA____Subset (Idv) Idv)

(declare-fun smt__TLA____SubsetEq (Idv Idv) Bool)

(declare-fun smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (Idv
  Idv) Bool)

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

; omitted fact (second-order)

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

;; Axiom: DisjointTrigger
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (smt__TLA____SetExtTrigger (smt__TLA____Cap smt__x smt__y)
          smt__TLA____SetEnum__0) :pattern ((smt__TLA____Cap smt__x smt__y))))
    :named |DisjointTrigger|))

; omitted fact (second-order)

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

;; Axiom: Typing TIntPlus
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (smt__TLA____IntPlus (smt__TLA____Cast__Int smt__x1)
            (smt__TLA____Cast__Int smt__x2))
          (smt__TLA____Cast__Int (+ smt__x1 smt__x2)))
        :pattern ((smt__TLA____IntPlus (smt__TLA____Cast__Int smt__x1)
                    (smt__TLA____Cast__Int smt__x2)))))
    :named |Typing TIntPlus|))

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

(declare-fun smt__CONSTANT__MaxTerm__ () Idv)

(declare-fun smt__CONSTANT__MaxLogLen__ () Idv)

(declare-fun smt__CONSTANT__MaxConfigVersion__ () Idv)

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__TLA____SetSt__flatnd__1 (Idv Idv) Idv)

;; Axiom: SetStDef TLA__SetSt_flatnd_1
(assert
  (!
    (forall ((smt__CONSTANT__i__ Idv) (smt__a Idv) (smt__x Idv))
      (!
        (=
          (smt__TLA____Mem smt__x
            (smt__TLA____SetSt__flatnd__1 smt__a smt__CONSTANT__i__))
          (and (smt__TLA____Mem smt__x smt__a)
            (and
              (smt__TLA____IntLteq
                (smt__CONSTANT__Cardinality__
                  (smt__TLA____FunApp smt__VARIABLE__config__
                    smt__CONSTANT__i__))
                (smt__TLA____IntTimes (smt__CONSTANT__Cardinality__ smt__x)
                  (smt__TLA____Cast__Int 2)))
              (distinct
                (smt__CONSTANT__Cardinality__
                  (smt__TLA____FunApp smt__VARIABLE__config__
                    smt__CONSTANT__i__))
                (smt__TLA____IntTimes (smt__CONSTANT__Cardinality__ smt__x)
                  (smt__TLA____Cast__Int 2))))))
        :pattern ((smt__TLA____Mem smt__x
                    (smt__TLA____SetSt__flatnd__1 smt__a smt__CONSTANT__i__)))
        :pattern ((smt__TLA____Mem smt__x smt__a)
                   (smt__TLA____SetSt__flatnd__1 smt__a smt__CONSTANT__i__))))
    :named |SetStDef TLA__SetSt_flatnd_1|))

(declare-fun smt__TLA____SetSt__flatnd__9 (Idv Idv) Idv)

;; Axiom: SetStDef TLA__SetSt_flatnd_9
(assert
  (!
    (forall ((smt__CONSTANT__newConfig__ Idv) (smt__a Idv) (smt__x Idv))
      (!
        (=
          (smt__TLA____Mem smt__x
            (smt__TLA____SetSt__flatnd__9 smt__a smt__CONSTANT__newConfig__))
          (and (smt__TLA____Mem smt__x smt__a)
            (and
              (smt__TLA____IntLteq
                (smt__CONSTANT__Cardinality__ smt__CONSTANT__newConfig__)
                (smt__TLA____IntTimes (smt__CONSTANT__Cardinality__ smt__x)
                  (smt__TLA____Cast__Int 2)))
              (distinct
                (smt__CONSTANT__Cardinality__ smt__CONSTANT__newConfig__)
                (smt__TLA____IntTimes (smt__CONSTANT__Cardinality__ smt__x)
                  (smt__TLA____Cast__Int 2))))))
        :pattern ((smt__TLA____Mem smt__x
                    (smt__TLA____SetSt__flatnd__9 smt__a
                      smt__CONSTANT__newConfig__)))
        :pattern ((smt__TLA____Mem smt__x smt__a)
                   (smt__TLA____SetSt__flatnd__9 smt__a
                     smt__CONSTANT__newConfig__))))
    :named |SetStDef TLA__SetSt_flatnd_9|))

(declare-fun smt__TLA____FunFcn__flatnd__11 (Idv Idv Idv) Idv)

;; Axiom: FunConstrIsafcn TLA__FunFcn_flatnd_11
(assert
  (!
    (forall ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__Q__ Idv) (smt__a Idv))
      (!
        (smt__TLA____FunIsafcn
          (smt__TLA____FunFcn__flatnd__11 smt__a smt__CONSTANT__i__
            smt__CONSTANT__Q__))
        :pattern ((smt__TLA____FunFcn__flatnd__11 smt__a smt__CONSTANT__i__
                    smt__CONSTANT__Q__))))
    :named |FunConstrIsafcn TLA__FunFcn_flatnd_11|))

;; Axiom: FunDomDef TLA__FunFcn_flatnd_11
(assert
  (!
    (forall ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__Q__ Idv) (smt__a Idv))
      (!
        (=
          (smt__TLA____FunDom
            (smt__TLA____FunFcn__flatnd__11 smt__a smt__CONSTANT__i__
              smt__CONSTANT__Q__)) smt__a)
        :pattern ((smt__TLA____FunFcn__flatnd__11 smt__a smt__CONSTANT__i__
                    smt__CONSTANT__Q__))))
    :named |FunDomDef TLA__FunFcn_flatnd_11|))

;; Axiom: FunAppDef TLA__FunFcn_flatnd_11
(assert
  (!
    (forall
      ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__Q__ Idv) (smt__a Idv)
        (smt__x Idv))
      (!
        (=> (smt__TLA____Mem smt__x smt__a)
          (=
            (smt__TLA____FunApp
              (smt__TLA____FunFcn__flatnd__11 smt__a smt__CONSTANT__i__
                smt__CONSTANT__Q__) smt__x)
            (ite (smt__TLA____Mem smt__x smt__CONSTANT__Q__)
              (smt__TLA____IntPlus
                (smt__TLA____FunApp smt__VARIABLE__currentTerm__
                  smt__CONSTANT__i__) (smt__TLA____Cast__Int 1))
              (smt__TLA____FunApp smt__VARIABLE__currentTerm__ smt__x))))
        :pattern ((smt__TLA____FunApp
                    (smt__TLA____FunFcn__flatnd__11 smt__a smt__CONSTANT__i__
                      smt__CONSTANT__Q__) smt__x))
        :pattern ((smt__TLA____Mem smt__x smt__a)
                   (smt__TLA____FunFcn__flatnd__11 smt__a smt__CONSTANT__i__
                     smt__CONSTANT__Q__))))
    :named |FunAppDef TLA__FunFcn_flatnd_11|))

;; Axiom: FunTyping TLA__FunFcn_flatnd_11
(assert
  (!
    (forall
      ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__Q__ Idv) (smt__a Idv)
        (smt__b Idv))
      (!
        (=>
          (forall ((smt__x Idv))
            (=> (smt__TLA____Mem smt__x smt__a)
              (smt__TLA____Mem
                (ite (smt__TLA____Mem smt__x smt__CONSTANT__Q__)
                  (smt__TLA____IntPlus
                    (smt__TLA____FunApp smt__VARIABLE__currentTerm__
                      smt__CONSTANT__i__) (smt__TLA____Cast__Int 1))
                  (smt__TLA____FunApp smt__VARIABLE__currentTerm__ smt__x))
                smt__b)))
          (smt__TLA____Mem
            (smt__TLA____FunFcn__flatnd__11 smt__a smt__CONSTANT__i__
              smt__CONSTANT__Q__) (smt__TLA____FunSet smt__a smt__b)))
        :pattern ((smt__TLA____FunFcn__flatnd__11 smt__a smt__CONSTANT__i__
                    smt__CONSTANT__Q__) (smt__TLA____FunSet smt__a smt__b))))
    :named |FunTyping TLA__FunFcn_flatnd_11|))

(declare-fun smt__TLA____FunFcn__flatnd__12 (Idv Idv Idv) Idv)

;; Axiom: FunConstrIsafcn TLA__FunFcn_flatnd_12
(assert
  (!
    (forall ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__Q__ Idv) (smt__a Idv))
      (!
        (smt__TLA____FunIsafcn
          (smt__TLA____FunFcn__flatnd__12 smt__a smt__CONSTANT__i__
            smt__CONSTANT__Q__))
        :pattern ((smt__TLA____FunFcn__flatnd__12 smt__a smt__CONSTANT__i__
                    smt__CONSTANT__Q__))))
    :named |FunConstrIsafcn TLA__FunFcn_flatnd_12|))

;; Axiom: FunDomDef TLA__FunFcn_flatnd_12
(assert
  (!
    (forall ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__Q__ Idv) (smt__a Idv))
      (!
        (=
          (smt__TLA____FunDom
            (smt__TLA____FunFcn__flatnd__12 smt__a smt__CONSTANT__i__
              smt__CONSTANT__Q__)) smt__a)
        :pattern ((smt__TLA____FunFcn__flatnd__12 smt__a smt__CONSTANT__i__
                    smt__CONSTANT__Q__))))
    :named |FunDomDef TLA__FunFcn_flatnd_12|))

;; Axiom: FunAppDef TLA__FunFcn_flatnd_12
(assert
  (!
    (forall
      ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__Q__ Idv) (smt__a Idv)
        (smt__x Idv))
      (!
        (=> (smt__TLA____Mem smt__x smt__a)
          (=
            (smt__TLA____FunApp
              (smt__TLA____FunFcn__flatnd__12 smt__a smt__CONSTANT__i__
                smt__CONSTANT__Q__) smt__x)
            (ite (= smt__x smt__CONSTANT__i__) smt__CONSTANT__Primary__
              (ite (smt__TLA____Mem smt__x smt__CONSTANT__Q__)
                smt__CONSTANT__Secondary__
                (smt__TLA____FunApp smt__VARIABLE__state__ smt__x)))))
        :pattern ((smt__TLA____FunApp
                    (smt__TLA____FunFcn__flatnd__12 smt__a smt__CONSTANT__i__
                      smt__CONSTANT__Q__) smt__x))
        :pattern ((smt__TLA____Mem smt__x smt__a)
                   (smt__TLA____FunFcn__flatnd__12 smt__a smt__CONSTANT__i__
                     smt__CONSTANT__Q__))))
    :named |FunAppDef TLA__FunFcn_flatnd_12|))

;; Axiom: FunTyping TLA__FunFcn_flatnd_12
(assert
  (!
    (forall
      ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__Q__ Idv) (smt__a Idv)
        (smt__b Idv))
      (!
        (=>
          (forall ((smt__x Idv))
            (=> (smt__TLA____Mem smt__x smt__a)
              (smt__TLA____Mem
                (ite (= smt__x smt__CONSTANT__i__) smt__CONSTANT__Primary__
                  (ite (smt__TLA____Mem smt__x smt__CONSTANT__Q__)
                    smt__CONSTANT__Secondary__
                    (smt__TLA____FunApp smt__VARIABLE__state__ smt__x)))
                smt__b)))
          (smt__TLA____Mem
            (smt__TLA____FunFcn__flatnd__12 smt__a smt__CONSTANT__i__
              smt__CONSTANT__Q__) (smt__TLA____FunSet smt__a smt__b)))
        :pattern ((smt__TLA____FunFcn__flatnd__12 smt__a smt__CONSTANT__i__
                    smt__CONSTANT__Q__) (smt__TLA____FunSet smt__a smt__b))))
    :named |FunTyping TLA__FunFcn_flatnd_12|))

(declare-fun smt__TLA____SetSt__flatnd__13 (Idv Idv) Idv)

;; Axiom: SetStDef TLA__SetSt_flatnd_13
(assert
  (!
    (forall ((smt__CONSTANT__i__ Idv) (smt__a Idv) (smt__x Idv))
      (!
        (=
          (smt__TLA____Mem smt__x
            (smt__TLA____SetSt__flatnd__13 smt__a smt__CONSTANT__i__))
          (and (smt__TLA____Mem smt__x smt__a)
            (and
              (smt__TLA____IntLteq
                (smt__CONSTANT__Cardinality__
                  (smt__TLA____FunApp smt__VARIABLE__config____prime
                    smt__CONSTANT__i__))
                (smt__TLA____IntTimes (smt__CONSTANT__Cardinality__ smt__x)
                  (smt__TLA____Cast__Int 2)))
              (distinct
                (smt__CONSTANT__Cardinality__
                  (smt__TLA____FunApp smt__VARIABLE__config____prime
                    smt__CONSTANT__i__))
                (smt__TLA____IntTimes (smt__CONSTANT__Cardinality__ smt__x)
                  (smt__TLA____Cast__Int 2))))))
        :pattern ((smt__TLA____Mem smt__x
                    (smt__TLA____SetSt__flatnd__13 smt__a smt__CONSTANT__i__)))
        :pattern ((smt__TLA____Mem smt__x smt__a)
                   (smt__TLA____SetSt__flatnd__13 smt__a smt__CONSTANT__i__))))
    :named |SetStDef TLA__SetSt_flatnd_13|))

;; Goal
(assert
  (!
    (not
      (=>
        (and
          (and
            (and
              (smt__TLA____Mem smt__VARIABLE__currentTerm__
                (smt__TLA____FunSet smt__CONSTANT__Server__
                  smt__TLA____NatSet))
              (smt__TLA____Mem smt__VARIABLE__state__
                (smt__TLA____FunSet smt__CONSTANT__Server__
                  (smt__TLA____SetEnum__2 smt__CONSTANT__Secondary__
                    smt__CONSTANT__Primary__)))
              (smt__TLA____Mem smt__VARIABLE__config__
                (smt__TLA____FunSet smt__CONSTANT__Server__
                  (smt__TLA____Subset smt__CONSTANT__Server__)))
              (smt__TLA____Mem smt__VARIABLE__configVersion__
                (smt__TLA____FunSet smt__CONSTANT__Server__
                  smt__TLA____NatSet))
              (smt__TLA____Mem smt__VARIABLE__configTerm__
                (smt__TLA____FunSet smt__CONSTANT__Server__
                  smt__TLA____NatSet)))
            (forall ((smt__CONSTANT__s__ Idv) (smt__CONSTANT__t__ Idv))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__s__ smt__CONSTANT__Server__)
                  (smt__TLA____Mem smt__CONSTANT__t__ smt__CONSTANT__Server__))
                (=>
                  (and
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__state__
                        smt__CONSTANT__s__) smt__CONSTANT__Primary__)
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__state__
                        smt__CONSTANT__t__) smt__CONSTANT__Primary__)
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__currentTerm__
                        smt__CONSTANT__s__)
                      (smt__TLA____FunApp smt__VARIABLE__currentTerm__
                        smt__CONSTANT__t__)))
                  (= smt__CONSTANT__s__ smt__CONSTANT__t__))))
            (forall ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Server__)
                  (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Server__))
                (or
                  (forall
                    ((smt__CONSTANT__qx__ Idv) (smt__CONSTANT__qy__ Idv))
                    (=>
                      (and
                        (smt__TLA____Mem smt__CONSTANT__qx__
                          (smt__TLA____SetSt__flatnd__1
                            (smt__TLA____Subset
                              (smt__TLA____FunApp smt__VARIABLE__config__
                                smt__CONSTANT__i__)) smt__CONSTANT__i__))
                        (smt__TLA____Mem smt__CONSTANT__qy__
                          (smt__TLA____SetSt__flatnd__1
                            (smt__TLA____Subset
                              (smt__TLA____FunApp smt__VARIABLE__config__
                                smt__CONSTANT__j__)) smt__CONSTANT__j__)))
                      (not
                        (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__
                          (smt__TLA____Cap smt__CONSTANT__qx__
                            smt__CONSTANT__qy__) smt__TLA____SetEnum__0))))
                  (or
                    (forall ((smt__CONSTANT__Q__ Idv))
                      (=>
                        (smt__TLA____Mem smt__CONSTANT__Q__
                          (smt__TLA____SetSt__flatnd__1
                            (smt__TLA____Subset
                              (smt__TLA____FunApp smt__VARIABLE__config__
                                smt__CONSTANT__i__)) smt__CONSTANT__i__))
                        (exists ((smt__CONSTANT__n__ Idv))
                          (and
                            (smt__TLA____Mem smt__CONSTANT__n__
                              smt__CONSTANT__Q__)
                            (or
                              (and
                                (smt__TLA____IntLteq
                                  (smt__TLA____FunApp
                                    (smt__TLA____Tuple__2
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion__
                                        smt__CONSTANT__i__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configTerm__
                                        smt__CONSTANT__i__))
                                    (smt__TLA____Cast__Int 2))
                                  (smt__TLA____FunApp
                                    (smt__TLA____Tuple__2
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion__
                                        smt__CONSTANT__n__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configTerm__
                                        smt__CONSTANT__n__))
                                    (smt__TLA____Cast__Int 2)))
                                (distinct
                                  (smt__TLA____FunApp
                                    (smt__TLA____Tuple__2
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion__
                                        smt__CONSTANT__i__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configTerm__
                                        smt__CONSTANT__i__))
                                    (smt__TLA____Cast__Int 2))
                                  (smt__TLA____FunApp
                                    (smt__TLA____Tuple__2
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion__
                                        smt__CONSTANT__n__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configTerm__
                                        smt__CONSTANT__n__))
                                    (smt__TLA____Cast__Int 2))))
                              (and
                                (=
                                  (smt__TLA____FunApp
                                    (smt__TLA____Tuple__2
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion__
                                        smt__CONSTANT__n__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configTerm__
                                        smt__CONSTANT__n__))
                                    (smt__TLA____Cast__Int 2))
                                  (smt__TLA____FunApp
                                    (smt__TLA____Tuple__2
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion__
                                        smt__CONSTANT__i__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configTerm__
                                        smt__CONSTANT__i__))
                                    (smt__TLA____Cast__Int 2)))
                                (and
                                  (smt__TLA____IntLteq
                                    (smt__TLA____FunApp
                                      (smt__TLA____Tuple__2
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configVersion__
                                          smt__CONSTANT__i__)
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configTerm__
                                          smt__CONSTANT__i__))
                                      (smt__TLA____Cast__Int 1))
                                    (smt__TLA____FunApp
                                      (smt__TLA____Tuple__2
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configVersion__
                                          smt__CONSTANT__n__)
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configTerm__
                                          smt__CONSTANT__n__))
                                      (smt__TLA____Cast__Int 1)))
                                  (distinct
                                    (smt__TLA____FunApp
                                      (smt__TLA____Tuple__2
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configVersion__
                                          smt__CONSTANT__i__)
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configTerm__
                                          smt__CONSTANT__i__))
                                      (smt__TLA____Cast__Int 1))
                                    (smt__TLA____FunApp
                                      (smt__TLA____Tuple__2
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configVersion__
                                          smt__CONSTANT__n__)
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configTerm__
                                          smt__CONSTANT__n__))
                                      (smt__TLA____Cast__Int 1))))))))))
                    (and
                      (forall ((smt__CONSTANT__Q__ Idv))
                        (=>
                          (smt__TLA____Mem smt__CONSTANT__Q__
                            (smt__TLA____SetSt__flatnd__1
                              (smt__TLA____Subset
                                (smt__TLA____FunApp smt__VARIABLE__config__
                                  smt__CONSTANT__j__)) smt__CONSTANT__j__))
                          (exists ((smt__CONSTANT__n__ Idv))
                            (and
                              (smt__TLA____Mem smt__CONSTANT__n__
                                smt__CONSTANT__Q__)
                              (or
                                (and
                                  (smt__TLA____IntLteq
                                    (smt__TLA____FunApp
                                      (smt__TLA____Tuple__2
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configVersion__
                                          smt__CONSTANT__j__)
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configTerm__
                                          smt__CONSTANT__j__))
                                      (smt__TLA____Cast__Int 2))
                                    (smt__TLA____FunApp
                                      (smt__TLA____Tuple__2
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configVersion__
                                          smt__CONSTANT__n__)
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configTerm__
                                          smt__CONSTANT__n__))
                                      (smt__TLA____Cast__Int 2)))
                                  (distinct
                                    (smt__TLA____FunApp
                                      (smt__TLA____Tuple__2
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configVersion__
                                          smt__CONSTANT__j__)
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configTerm__
                                          smt__CONSTANT__j__))
                                      (smt__TLA____Cast__Int 2))
                                    (smt__TLA____FunApp
                                      (smt__TLA____Tuple__2
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configVersion__
                                          smt__CONSTANT__n__)
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configTerm__
                                          smt__CONSTANT__n__))
                                      (smt__TLA____Cast__Int 2))))
                                (and
                                  (=
                                    (smt__TLA____FunApp
                                      (smt__TLA____Tuple__2
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configVersion__
                                          smt__CONSTANT__n__)
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configTerm__
                                          smt__CONSTANT__n__))
                                      (smt__TLA____Cast__Int 2))
                                    (smt__TLA____FunApp
                                      (smt__TLA____Tuple__2
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configVersion__
                                          smt__CONSTANT__j__)
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configTerm__
                                          smt__CONSTANT__j__))
                                      (smt__TLA____Cast__Int 2)))
                                  (and
                                    (smt__TLA____IntLteq
                                      (smt__TLA____FunApp
                                        (smt__TLA____Tuple__2
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configVersion__
                                            smt__CONSTANT__j__)
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configTerm__
                                            smt__CONSTANT__j__))
                                        (smt__TLA____Cast__Int 1))
                                      (smt__TLA____FunApp
                                        (smt__TLA____Tuple__2
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configVersion__
                                            smt__CONSTANT__n__)
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configTerm__
                                            smt__CONSTANT__n__))
                                        (smt__TLA____Cast__Int 1)))
                                    (distinct
                                      (smt__TLA____FunApp
                                        (smt__TLA____Tuple__2
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configVersion__
                                            smt__CONSTANT__j__)
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configTerm__
                                            smt__CONSTANT__j__))
                                        (smt__TLA____Cast__Int 1))
                                      (smt__TLA____FunApp
                                        (smt__TLA____Tuple__2
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configVersion__
                                            smt__CONSTANT__n__)
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configTerm__
                                            smt__CONSTANT__n__))
                                        (smt__TLA____Cast__Int 1))))))))))
                      true)))))
            (forall ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Server__)
                  (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Server__))
                (or
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__config__
                      smt__CONSTANT__i__)
                    (smt__TLA____FunApp smt__VARIABLE__config__
                      smt__CONSTANT__j__))
                  (or
                    (or
                      (and
                        (smt__TLA____IntLteq
                          (smt__TLA____FunApp smt__VARIABLE__configTerm__
                            smt__CONSTANT__i__)
                          (smt__TLA____FunApp smt__VARIABLE__configTerm__
                            smt__CONSTANT__j__))
                        (distinct
                          (smt__TLA____FunApp smt__VARIABLE__configTerm__
                            smt__CONSTANT__i__)
                          (smt__TLA____FunApp smt__VARIABLE__configTerm__
                            smt__CONSTANT__j__)))
                      (and
                        (=
                          (smt__TLA____FunApp smt__VARIABLE__configTerm__
                            smt__CONSTANT__j__)
                          (smt__TLA____FunApp smt__VARIABLE__configTerm__
                            smt__CONSTANT__i__))
                        (and
                          (smt__TLA____IntLteq
                            (smt__TLA____FunApp
                              smt__VARIABLE__configVersion__
                              smt__CONSTANT__i__)
                            (smt__TLA____FunApp
                              smt__VARIABLE__configVersion__
                              smt__CONSTANT__j__))
                          (distinct
                            (smt__TLA____FunApp
                              smt__VARIABLE__configVersion__
                              smt__CONSTANT__i__)
                            (smt__TLA____FunApp
                              smt__VARIABLE__configVersion__
                              smt__CONSTANT__j__)))))
                    (and
                      (or
                        (and
                          (smt__TLA____IntLteq
                            (smt__TLA____FunApp smt__VARIABLE__configTerm__
                              smt__CONSTANT__j__)
                            (smt__TLA____FunApp smt__VARIABLE__configTerm__
                              smt__CONSTANT__i__))
                          (distinct
                            (smt__TLA____FunApp smt__VARIABLE__configTerm__
                              smt__CONSTANT__j__)
                            (smt__TLA____FunApp smt__VARIABLE__configTerm__
                              smt__CONSTANT__i__)))
                        (and
                          (=
                            (smt__TLA____FunApp smt__VARIABLE__configTerm__
                              smt__CONSTANT__i__)
                            (smt__TLA____FunApp smt__VARIABLE__configTerm__
                              smt__CONSTANT__j__))
                          (and
                            (smt__TLA____IntLteq
                              (smt__TLA____FunApp
                                smt__VARIABLE__configVersion__
                                smt__CONSTANT__j__)
                              (smt__TLA____FunApp
                                smt__VARIABLE__configVersion__
                                smt__CONSTANT__i__))
                            (distinct
                              (smt__TLA____FunApp
                                smt__VARIABLE__configVersion__
                                smt__CONSTANT__j__)
                              (smt__TLA____FunApp
                                smt__VARIABLE__configVersion__
                                smt__CONSTANT__i__))))) true)))))
            (forall ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Server__)
                  (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Server__))
                (or
                  (not
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__configTerm__
                        smt__CONSTANT__i__)
                      (smt__TLA____FunApp smt__VARIABLE__configTerm__
                        smt__CONSTANT__j__)))
                  (or
                    (not
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__state__
                          smt__CONSTANT__i__) smt__CONSTANT__Primary__))
                    (and
                      (not
                        (or
                          (and
                            (smt__TLA____IntLteq
                              (smt__TLA____FunApp smt__VARIABLE__configTerm__
                                smt__CONSTANT__i__)
                              (smt__TLA____FunApp smt__VARIABLE__configTerm__
                                smt__CONSTANT__j__))
                            (distinct
                              (smt__TLA____FunApp smt__VARIABLE__configTerm__
                                smt__CONSTANT__i__)
                              (smt__TLA____FunApp smt__VARIABLE__configTerm__
                                smt__CONSTANT__j__)))
                          (and
                            (=
                              (smt__TLA____FunApp smt__VARIABLE__configTerm__
                                smt__CONSTANT__j__)
                              (smt__TLA____FunApp smt__VARIABLE__configTerm__
                                smt__CONSTANT__i__))
                            (and
                              (smt__TLA____IntLteq
                                (smt__TLA____FunApp
                                  smt__VARIABLE__configVersion__
                                  smt__CONSTANT__i__)
                                (smt__TLA____FunApp
                                  smt__VARIABLE__configVersion__
                                  smt__CONSTANT__j__))
                              (distinct
                                (smt__TLA____FunApp
                                  smt__VARIABLE__configVersion__
                                  smt__CONSTANT__i__)
                                (smt__TLA____FunApp
                                  smt__VARIABLE__configVersion__
                                  smt__CONSTANT__j__)))))) true)))))
            (forall ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Server__)
                  (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Server__))
                (forall ((smt__CONSTANT__Q__ Idv))
                  (=>
                    (smt__TLA____Mem smt__CONSTANT__Q__
                      (smt__TLA____SetSt__flatnd__1
                        (smt__TLA____Subset
                          (smt__TLA____FunApp smt__VARIABLE__config__
                            smt__CONSTANT__j__)) smt__CONSTANT__j__))
                    (exists ((smt__CONSTANT__n__ Idv))
                      (and
                        (smt__TLA____Mem smt__CONSTANT__n__
                          smt__CONSTANT__Q__)
                        (or
                          (smt__TLA____IntLteq
                            (smt__TLA____FunApp smt__VARIABLE__configTerm__
                              smt__CONSTANT__i__)
                            (smt__TLA____FunApp smt__VARIABLE__currentTerm__
                              smt__CONSTANT__n__))
                          (forall ((smt__CONSTANT__Q___1 Idv))
                            (=>
                              (smt__TLA____Mem smt__CONSTANT__Q___1
                                (smt__TLA____SetSt__flatnd__1
                                  (smt__TLA____Subset
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__config__
                                      smt__CONSTANT__j__)) smt__CONSTANT__j__))
                              (exists ((smt__CONSTANT__n___1 Idv))
                                (and
                                  (smt__TLA____Mem smt__CONSTANT__n___1
                                    smt__CONSTANT__Q___1)
                                  (or
                                    (and
                                      (smt__TLA____IntLteq
                                        (smt__TLA____FunApp
                                          (smt__TLA____Tuple__2
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configVersion__
                                              smt__CONSTANT__j__)
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configTerm__
                                              smt__CONSTANT__j__))
                                          (smt__TLA____Cast__Int 2))
                                        (smt__TLA____FunApp
                                          (smt__TLA____Tuple__2
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configVersion__
                                              smt__CONSTANT__n___1)
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configTerm__
                                              smt__CONSTANT__n___1))
                                          (smt__TLA____Cast__Int 2)))
                                      (distinct
                                        (smt__TLA____FunApp
                                          (smt__TLA____Tuple__2
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configVersion__
                                              smt__CONSTANT__j__)
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configTerm__
                                              smt__CONSTANT__j__))
                                          (smt__TLA____Cast__Int 2))
                                        (smt__TLA____FunApp
                                          (smt__TLA____Tuple__2
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configVersion__
                                              smt__CONSTANT__n___1)
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configTerm__
                                              smt__CONSTANT__n___1))
                                          (smt__TLA____Cast__Int 2))))
                                    (and
                                      (=
                                        (smt__TLA____FunApp
                                          (smt__TLA____Tuple__2
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configVersion__
                                              smt__CONSTANT__n___1)
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configTerm__
                                              smt__CONSTANT__n___1))
                                          (smt__TLA____Cast__Int 2))
                                        (smt__TLA____FunApp
                                          (smt__TLA____Tuple__2
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configVersion__
                                              smt__CONSTANT__j__)
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configTerm__
                                              smt__CONSTANT__j__))
                                          (smt__TLA____Cast__Int 2)))
                                      (and
                                        (smt__TLA____IntLteq
                                          (smt__TLA____FunApp
                                            (smt__TLA____Tuple__2
                                              (smt__TLA____FunApp
                                                smt__VARIABLE__configVersion__
                                                smt__CONSTANT__j__)
                                              (smt__TLA____FunApp
                                                smt__VARIABLE__configTerm__
                                                smt__CONSTANT__j__))
                                            (smt__TLA____Cast__Int 1))
                                          (smt__TLA____FunApp
                                            (smt__TLA____Tuple__2
                                              (smt__TLA____FunApp
                                                smt__VARIABLE__configVersion__
                                                smt__CONSTANT__n___1)
                                              (smt__TLA____FunApp
                                                smt__VARIABLE__configTerm__
                                                smt__CONSTANT__n___1))
                                            (smt__TLA____Cast__Int 1)))
                                        (distinct
                                          (smt__TLA____FunApp
                                            (smt__TLA____Tuple__2
                                              (smt__TLA____FunApp
                                                smt__VARIABLE__configVersion__
                                                smt__CONSTANT__j__)
                                              (smt__TLA____FunApp
                                                smt__VARIABLE__configTerm__
                                                smt__CONSTANT__j__))
                                            (smt__TLA____Cast__Int 1))
                                          (smt__TLA____FunApp
                                            (smt__TLA____Tuple__2
                                              (smt__TLA____FunApp
                                                smt__VARIABLE__configVersion__
                                                smt__CONSTANT__n___1)
                                              (smt__TLA____FunApp
                                                smt__VARIABLE__configTerm__
                                                smt__CONSTANT__n___1))
                                            (smt__TLA____Cast__Int 1)))))))))))))))))
            (forall ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
              (=>
                (and
                  (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Server__)
                  (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Server__))
                (or
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__configTerm__
                      smt__CONSTANT__j__)
                    (smt__TLA____FunApp smt__VARIABLE__currentTerm__
                      smt__CONSTANT__j__))
                  (and
                    (not
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__state__
                          smt__CONSTANT__j__) smt__CONSTANT__Primary__)) 
                    true)))))
          (or
            (exists
              ((smt__CONSTANT__s__ Idv) (smt__CONSTANT__newConfig__ Idv))
              (and
                (smt__TLA____Mem smt__CONSTANT__s__ smt__CONSTANT__Server__)
                (smt__TLA____Mem smt__CONSTANT__newConfig__
                  (smt__TLA____Subset smt__CONSTANT__Server__))
                (and
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__state__
                      smt__CONSTANT__s__) smt__CONSTANT__Primary__)
                  (and
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__state__
                        smt__CONSTANT__s__) smt__CONSTANT__Primary__)
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__configTerm__
                        smt__CONSTANT__s__)
                      (smt__TLA____FunApp smt__VARIABLE__currentTerm__
                        smt__CONSTANT__s__))
                    (exists ((smt__CONSTANT__Q__ Idv))
                      (and
                        (smt__TLA____Mem smt__CONSTANT__Q__
                          (smt__TLA____SetSt__flatnd__1
                            (smt__TLA____Subset
                              (smt__TLA____FunApp smt__VARIABLE__config__
                                smt__CONSTANT__s__)) smt__CONSTANT__s__))
                        (forall ((smt__CONSTANT__t__ Idv))
                          (=>
                            (smt__TLA____Mem smt__CONSTANT__t__
                              smt__CONSTANT__Q__)
                            (and
                              (=
                                (smt__TLA____FunApp
                                  smt__VARIABLE__configVersion__
                                  smt__CONSTANT__s__)
                                (smt__TLA____FunApp
                                  smt__VARIABLE__configVersion__
                                  smt__CONSTANT__t__))
                              (=
                                (smt__TLA____FunApp
                                  smt__VARIABLE__configTerm__
                                  smt__CONSTANT__s__)
                                (smt__TLA____FunApp
                                  smt__VARIABLE__configTerm__
                                  smt__CONSTANT__t__))
                              (=
                                (smt__TLA____FunApp
                                  smt__VARIABLE__currentTerm__
                                  smt__CONSTANT__t__)
                                (smt__TLA____FunApp
                                  smt__VARIABLE__currentTerm__
                                  smt__CONSTANT__s__))))))))
                  (forall
                    ((smt__CONSTANT__qx__ Idv) (smt__CONSTANT__qy__ Idv))
                    (=>
                      (and
                        (smt__TLA____Mem smt__CONSTANT__qx__
                          (smt__TLA____SetSt__flatnd__1
                            (smt__TLA____Subset
                              (smt__TLA____FunApp smt__VARIABLE__config__
                                smt__CONSTANT__s__)) smt__CONSTANT__s__))
                        (smt__TLA____Mem smt__CONSTANT__qy__
                          (smt__TLA____SetSt__flatnd__9
                            (smt__TLA____Subset smt__CONSTANT__newConfig__)
                            smt__CONSTANT__newConfig__)))
                      (not
                        (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__
                          (smt__TLA____Cap smt__CONSTANT__qx__
                            smt__CONSTANT__qy__) smt__TLA____SetEnum__0))))
                  (smt__TLA____Mem smt__CONSTANT__s__
                    smt__CONSTANT__newConfig__)
                  (= smt__VARIABLE__configTerm____prime
                    (smt__TLA____FunExcept smt__VARIABLE__configTerm__
                      smt__CONSTANT__s__
                      (smt__TLA____FunApp smt__VARIABLE__currentTerm__
                        smt__CONSTANT__s__)))
                  (= smt__VARIABLE__configVersion____prime
                    (smt__TLA____FunExcept smt__VARIABLE__configVersion__
                      smt__CONSTANT__s__
                      (smt__TLA____IntPlus
                        (smt__TLA____FunApp smt__VARIABLE__configVersion__
                          smt__CONSTANT__s__) (smt__TLA____Cast__Int 1))))
                  (= smt__VARIABLE__config____prime
                    (smt__TLA____FunExcept smt__VARIABLE__config__
                      smt__CONSTANT__s__ smt__CONSTANT__newConfig__))
                  (and
                    (= smt__VARIABLE__currentTerm____prime
                      smt__VARIABLE__currentTerm__)
                    (= smt__VARIABLE__state____prime smt__VARIABLE__state__)))))
            (exists ((smt__CONSTANT__s__ Idv) (smt__CONSTANT__t__ Idv))
              (and
                (smt__TLA____Mem smt__CONSTANT__s__ smt__CONSTANT__Server__)
                (smt__TLA____Mem smt__CONSTANT__t__ smt__CONSTANT__Server__)
                (and
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__state__
                      smt__CONSTANT__t__) smt__CONSTANT__Secondary__)
                  (or
                    (and
                      (smt__TLA____IntLteq
                        (smt__TLA____FunApp smt__VARIABLE__configTerm__
                          smt__CONSTANT__t__)
                        (smt__TLA____FunApp smt__VARIABLE__configTerm__
                          smt__CONSTANT__s__))
                      (distinct
                        (smt__TLA____FunApp smt__VARIABLE__configTerm__
                          smt__CONSTANT__t__)
                        (smt__TLA____FunApp smt__VARIABLE__configTerm__
                          smt__CONSTANT__s__)))
                    (and
                      (=
                        (smt__TLA____FunApp smt__VARIABLE__configTerm__
                          smt__CONSTANT__s__)
                        (smt__TLA____FunApp smt__VARIABLE__configTerm__
                          smt__CONSTANT__t__))
                      (and
                        (smt__TLA____IntLteq
                          (smt__TLA____FunApp smt__VARIABLE__configVersion__
                            smt__CONSTANT__t__)
                          (smt__TLA____FunApp smt__VARIABLE__configVersion__
                            smt__CONSTANT__s__))
                        (distinct
                          (smt__TLA____FunApp smt__VARIABLE__configVersion__
                            smt__CONSTANT__t__)
                          (smt__TLA____FunApp smt__VARIABLE__configVersion__
                            smt__CONSTANT__s__)))))
                  (= smt__VARIABLE__configVersion____prime
                    (smt__TLA____FunExcept smt__VARIABLE__configVersion__
                      smt__CONSTANT__t__
                      (smt__TLA____FunApp smt__VARIABLE__configVersion__
                        smt__CONSTANT__s__)))
                  (= smt__VARIABLE__configTerm____prime
                    (smt__TLA____FunExcept smt__VARIABLE__configTerm__
                      smt__CONSTANT__t__
                      (smt__TLA____FunApp smt__VARIABLE__configTerm__
                        smt__CONSTANT__s__)))
                  (= smt__VARIABLE__config____prime
                    (smt__TLA____FunExcept smt__VARIABLE__config__
                      smt__CONSTANT__t__
                      (smt__TLA____FunApp smt__VARIABLE__config__
                        smt__CONSTANT__s__)))
                  (and
                    (= smt__VARIABLE__currentTerm____prime
                      smt__VARIABLE__currentTerm__)
                    (= smt__VARIABLE__state____prime smt__VARIABLE__state__)))))
            (exists ((smt__CONSTANT__i__ Idv))
              (and
                (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Server__)
                (exists ((smt__CONSTANT__Q__ Idv))
                  (and
                    (smt__TLA____Mem smt__CONSTANT__Q__
                      (smt__TLA____SetSt__flatnd__1
                        (smt__TLA____Subset
                          (smt__TLA____FunApp smt__VARIABLE__config__
                            smt__CONSTANT__i__)) smt__CONSTANT__i__))
                    (and
                      (smt__TLA____Mem smt__CONSTANT__i__
                        (smt__TLA____FunApp smt__VARIABLE__config__
                          smt__CONSTANT__i__))
                      (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Q__)
                      (forall ((smt__CONSTANT__v__ Idv))
                        (=>
                          (smt__TLA____Mem smt__CONSTANT__v__
                            smt__CONSTANT__Q__)
                          (and
                            (and
                              (smt__TLA____IntLteq
                                (smt__TLA____FunApp
                                  smt__VARIABLE__currentTerm__
                                  smt__CONSTANT__v__)
                                (smt__TLA____IntPlus
                                  (smt__TLA____FunApp
                                    smt__VARIABLE__currentTerm__
                                    smt__CONSTANT__i__)
                                  (smt__TLA____Cast__Int 1)))
                              (distinct
                                (smt__TLA____FunApp
                                  smt__VARIABLE__currentTerm__
                                  smt__CONSTANT__v__)
                                (smt__TLA____IntPlus
                                  (smt__TLA____FunApp
                                    smt__VARIABLE__currentTerm__
                                    smt__CONSTANT__i__)
                                  (smt__TLA____Cast__Int 1))))
                            (or
                              (and
                                (=
                                  (smt__TLA____FunApp
                                    smt__VARIABLE__configTerm__
                                    smt__CONSTANT__i__)
                                  (smt__TLA____FunApp
                                    smt__VARIABLE__configTerm__
                                    smt__CONSTANT__v__))
                                (=
                                  (smt__TLA____FunApp
                                    smt__VARIABLE__configVersion__
                                    smt__CONSTANT__i__)
                                  (smt__TLA____FunApp
                                    smt__VARIABLE__configVersion__
                                    smt__CONSTANT__v__)))
                              (or
                                (and
                                  (smt__TLA____IntLteq
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configTerm__
                                      smt__CONSTANT__v__)
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configTerm__
                                      smt__CONSTANT__i__))
                                  (distinct
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configTerm__
                                      smt__CONSTANT__v__)
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configTerm__
                                      smt__CONSTANT__i__)))
                                (and
                                  (=
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configTerm__
                                      smt__CONSTANT__i__)
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configTerm__
                                      smt__CONSTANT__v__))
                                  (and
                                    (smt__TLA____IntLteq
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion__
                                        smt__CONSTANT__v__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion__
                                        smt__CONSTANT__i__))
                                    (distinct
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion__
                                        smt__CONSTANT__v__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion__
                                        smt__CONSTANT__i__)))))))))
                      (= smt__VARIABLE__currentTerm____prime
                        (smt__TLA____FunFcn__flatnd__11
                          smt__CONSTANT__Server__ smt__CONSTANT__i__
                          smt__CONSTANT__Q__))
                      (= smt__VARIABLE__state____prime
                        (smt__TLA____FunFcn__flatnd__12
                          smt__CONSTANT__Server__ smt__CONSTANT__i__
                          smt__CONSTANT__Q__))
                      (= smt__VARIABLE__configTerm____prime
                        (smt__TLA____FunExcept smt__VARIABLE__configTerm__
                          smt__CONSTANT__i__
                          (smt__TLA____IntPlus
                            (smt__TLA____FunApp smt__VARIABLE__currentTerm__
                              smt__CONSTANT__i__) (smt__TLA____Cast__Int 1))))
                      (and
                        (= smt__VARIABLE__config____prime
                          smt__VARIABLE__config__)
                        (= smt__VARIABLE__configVersion____prime
                          smt__VARIABLE__configVersion__)))))))
            (exists ((smt__CONSTANT__s__ Idv) (smt__CONSTANT__t__ Idv))
              (and
                (smt__TLA____Mem smt__CONSTANT__s__ smt__CONSTANT__Server__)
                (smt__TLA____Mem smt__CONSTANT__t__ smt__CONSTANT__Server__)
                (and
                  (and
                    (and
                      (smt__TLA____IntLteq
                        (smt__TLA____FunApp smt__VARIABLE__currentTerm__
                          smt__CONSTANT__t__)
                        (smt__TLA____FunApp smt__VARIABLE__currentTerm__
                          smt__CONSTANT__s__))
                      (distinct
                        (smt__TLA____FunApp smt__VARIABLE__currentTerm__
                          smt__CONSTANT__t__)
                        (smt__TLA____FunApp smt__VARIABLE__currentTerm__
                          smt__CONSTANT__s__)))
                    (= smt__VARIABLE__currentTerm____prime
                      (smt__TLA____FunExcept smt__VARIABLE__currentTerm__
                        smt__CONSTANT__t__
                        (smt__TLA____FunApp smt__VARIABLE__currentTerm__
                          smt__CONSTANT__s__)))
                    (= smt__VARIABLE__state____prime
                      (smt__TLA____FunExcept smt__VARIABLE__state__
                        smt__CONSTANT__t__ smt__CONSTANT__Secondary__)))
                  (and
                    (= smt__VARIABLE__configVersion____prime
                      smt__VARIABLE__configVersion__)
                    (= smt__VARIABLE__configTerm____prime
                      smt__VARIABLE__configTerm__)
                    (= smt__VARIABLE__config____prime smt__VARIABLE__config__)))))))
        (and
          (and
            (smt__TLA____Mem smt__VARIABLE__currentTerm____prime
              (smt__TLA____FunSet smt__CONSTANT__Server__ smt__TLA____NatSet))
            (smt__TLA____Mem smt__VARIABLE__state____prime
              (smt__TLA____FunSet smt__CONSTANT__Server__
                (smt__TLA____SetEnum__2 smt__CONSTANT__Secondary__
                  smt__CONSTANT__Primary__)))
            (smt__TLA____Mem smt__VARIABLE__config____prime
              (smt__TLA____FunSet smt__CONSTANT__Server__
                (smt__TLA____Subset smt__CONSTANT__Server__)))
            (smt__TLA____Mem smt__VARIABLE__configVersion____prime
              (smt__TLA____FunSet smt__CONSTANT__Server__ smt__TLA____NatSet))
            (smt__TLA____Mem smt__VARIABLE__configTerm____prime
              (smt__TLA____FunSet smt__CONSTANT__Server__ smt__TLA____NatSet)))
          (forall ((smt__CONSTANT__s__ Idv) (smt__CONSTANT__t__ Idv))
            (=>
              (and
                (smt__TLA____Mem smt__CONSTANT__s__ smt__CONSTANT__Server__)
                (smt__TLA____Mem smt__CONSTANT__t__ smt__CONSTANT__Server__))
              (=>
                (and
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__state____prime
                      smt__CONSTANT__s__) smt__CONSTANT__Primary__)
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__state____prime
                      smt__CONSTANT__t__) smt__CONSTANT__Primary__)
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__currentTerm____prime
                      smt__CONSTANT__s__)
                    (smt__TLA____FunApp smt__VARIABLE__currentTerm____prime
                      smt__CONSTANT__t__)))
                (= smt__CONSTANT__s__ smt__CONSTANT__t__))))
          (forall ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
            (=>
              (and
                (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Server__)
                (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Server__))
              (or
                (forall ((smt__CONSTANT__qx__ Idv) (smt__CONSTANT__qy__ Idv))
                  (=>
                    (and
                      (smt__TLA____Mem smt__CONSTANT__qx__
                        (smt__TLA____SetSt__flatnd__13
                          (smt__TLA____Subset
                            (smt__TLA____FunApp
                              smt__VARIABLE__config____prime
                              smt__CONSTANT__i__)) smt__CONSTANT__i__))
                      (smt__TLA____Mem smt__CONSTANT__qy__
                        (smt__TLA____SetSt__flatnd__13
                          (smt__TLA____Subset
                            (smt__TLA____FunApp
                              smt__VARIABLE__config____prime
                              smt__CONSTANT__j__)) smt__CONSTANT__j__)))
                    (distinct
                      (smt__TLA____Cap smt__CONSTANT__qx__
                        smt__CONSTANT__qy__) smt__TLA____SetEnum__0)))
                (or
                  (forall ((smt__CONSTANT__Q__ Idv))
                    (=>
                      (smt__TLA____Mem smt__CONSTANT__Q__
                        (smt__TLA____SetSt__flatnd__13
                          (smt__TLA____Subset
                            (smt__TLA____FunApp
                              smt__VARIABLE__config____prime
                              smt__CONSTANT__i__)) smt__CONSTANT__i__))
                      (exists ((smt__CONSTANT__n__ Idv))
                        (and
                          (smt__TLA____Mem smt__CONSTANT__n__
                            smt__CONSTANT__Q__)
                          (or
                            (and
                              (smt__TLA____IntLteq
                                (smt__TLA____FunApp
                                  (smt__TLA____Tuple__2
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configVersion____prime
                                      smt__CONSTANT__i__)
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configTerm____prime
                                      smt__CONSTANT__i__))
                                  (smt__TLA____Cast__Int 2))
                                (smt__TLA____FunApp
                                  (smt__TLA____Tuple__2
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configVersion____prime
                                      smt__CONSTANT__n__)
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configTerm____prime
                                      smt__CONSTANT__n__))
                                  (smt__TLA____Cast__Int 2)))
                              (distinct
                                (smt__TLA____FunApp
                                  (smt__TLA____Tuple__2
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configVersion____prime
                                      smt__CONSTANT__i__)
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configTerm____prime
                                      smt__CONSTANT__i__))
                                  (smt__TLA____Cast__Int 2))
                                (smt__TLA____FunApp
                                  (smt__TLA____Tuple__2
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configVersion____prime
                                      smt__CONSTANT__n__)
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configTerm____prime
                                      smt__CONSTANT__n__))
                                  (smt__TLA____Cast__Int 2))))
                            (and
                              (=
                                (smt__TLA____FunApp
                                  (smt__TLA____Tuple__2
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configVersion____prime
                                      smt__CONSTANT__n__)
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configTerm____prime
                                      smt__CONSTANT__n__))
                                  (smt__TLA____Cast__Int 2))
                                (smt__TLA____FunApp
                                  (smt__TLA____Tuple__2
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configVersion____prime
                                      smt__CONSTANT__i__)
                                    (smt__TLA____FunApp
                                      smt__VARIABLE__configTerm____prime
                                      smt__CONSTANT__i__))
                                  (smt__TLA____Cast__Int 2)))
                              (and
                                (smt__TLA____IntLteq
                                  (smt__TLA____FunApp
                                    (smt__TLA____Tuple__2
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion____prime
                                        smt__CONSTANT__i__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configTerm____prime
                                        smt__CONSTANT__i__))
                                    (smt__TLA____Cast__Int 1))
                                  (smt__TLA____FunApp
                                    (smt__TLA____Tuple__2
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion____prime
                                        smt__CONSTANT__n__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configTerm____prime
                                        smt__CONSTANT__n__))
                                    (smt__TLA____Cast__Int 1)))
                                (distinct
                                  (smt__TLA____FunApp
                                    (smt__TLA____Tuple__2
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion____prime
                                        smt__CONSTANT__i__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configTerm____prime
                                        smt__CONSTANT__i__))
                                    (smt__TLA____Cast__Int 1))
                                  (smt__TLA____FunApp
                                    (smt__TLA____Tuple__2
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion____prime
                                        smt__CONSTANT__n__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configTerm____prime
                                        smt__CONSTANT__n__))
                                    (smt__TLA____Cast__Int 1))))))))))
                  (and
                    (forall ((smt__CONSTANT__Q__ Idv))
                      (=>
                        (smt__TLA____Mem smt__CONSTANT__Q__
                          (smt__TLA____SetSt__flatnd__13
                            (smt__TLA____Subset
                              (smt__TLA____FunApp
                                smt__VARIABLE__config____prime
                                smt__CONSTANT__j__)) smt__CONSTANT__j__))
                        (exists ((smt__CONSTANT__n__ Idv))
                          (and
                            (smt__TLA____Mem smt__CONSTANT__n__
                              smt__CONSTANT__Q__)
                            (or
                              (and
                                (smt__TLA____IntLteq
                                  (smt__TLA____FunApp
                                    (smt__TLA____Tuple__2
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion____prime
                                        smt__CONSTANT__j__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configTerm____prime
                                        smt__CONSTANT__j__))
                                    (smt__TLA____Cast__Int 2))
                                  (smt__TLA____FunApp
                                    (smt__TLA____Tuple__2
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion____prime
                                        smt__CONSTANT__n__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configTerm____prime
                                        smt__CONSTANT__n__))
                                    (smt__TLA____Cast__Int 2)))
                                (distinct
                                  (smt__TLA____FunApp
                                    (smt__TLA____Tuple__2
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion____prime
                                        smt__CONSTANT__j__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configTerm____prime
                                        smt__CONSTANT__j__))
                                    (smt__TLA____Cast__Int 2))
                                  (smt__TLA____FunApp
                                    (smt__TLA____Tuple__2
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion____prime
                                        smt__CONSTANT__n__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configTerm____prime
                                        smt__CONSTANT__n__))
                                    (smt__TLA____Cast__Int 2))))
                              (and
                                (=
                                  (smt__TLA____FunApp
                                    (smt__TLA____Tuple__2
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion____prime
                                        smt__CONSTANT__n__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configTerm____prime
                                        smt__CONSTANT__n__))
                                    (smt__TLA____Cast__Int 2))
                                  (smt__TLA____FunApp
                                    (smt__TLA____Tuple__2
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configVersion____prime
                                        smt__CONSTANT__j__)
                                      (smt__TLA____FunApp
                                        smt__VARIABLE__configTerm____prime
                                        smt__CONSTANT__j__))
                                    (smt__TLA____Cast__Int 2)))
                                (and
                                  (smt__TLA____IntLteq
                                    (smt__TLA____FunApp
                                      (smt__TLA____Tuple__2
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configVersion____prime
                                          smt__CONSTANT__j__)
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configTerm____prime
                                          smt__CONSTANT__j__))
                                      (smt__TLA____Cast__Int 1))
                                    (smt__TLA____FunApp
                                      (smt__TLA____Tuple__2
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configVersion____prime
                                          smt__CONSTANT__n__)
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configTerm____prime
                                          smt__CONSTANT__n__))
                                      (smt__TLA____Cast__Int 1)))
                                  (distinct
                                    (smt__TLA____FunApp
                                      (smt__TLA____Tuple__2
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configVersion____prime
                                          smt__CONSTANT__j__)
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configTerm____prime
                                          smt__CONSTANT__j__))
                                      (smt__TLA____Cast__Int 1))
                                    (smt__TLA____FunApp
                                      (smt__TLA____Tuple__2
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configVersion____prime
                                          smt__CONSTANT__n__)
                                        (smt__TLA____FunApp
                                          smt__VARIABLE__configTerm____prime
                                          smt__CONSTANT__n__))
                                      (smt__TLA____Cast__Int 1)))))))))) 
                    true)))))
          (forall ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
            (=>
              (and
                (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Server__)
                (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Server__))
              (or
                (=
                  (smt__TLA____FunApp smt__VARIABLE__config____prime
                    smt__CONSTANT__i__)
                  (smt__TLA____FunApp smt__VARIABLE__config____prime
                    smt__CONSTANT__j__))
                (or
                  (or
                    (and
                      (smt__TLA____IntLteq
                        (smt__TLA____FunApp
                          smt__VARIABLE__configTerm____prime
                          smt__CONSTANT__i__)
                        (smt__TLA____FunApp
                          smt__VARIABLE__configTerm____prime
                          smt__CONSTANT__j__))
                      (distinct
                        (smt__TLA____FunApp
                          smt__VARIABLE__configTerm____prime
                          smt__CONSTANT__i__)
                        (smt__TLA____FunApp
                          smt__VARIABLE__configTerm____prime
                          smt__CONSTANT__j__)))
                    (and
                      (=
                        (smt__TLA____FunApp
                          smt__VARIABLE__configTerm____prime
                          smt__CONSTANT__j__)
                        (smt__TLA____FunApp
                          smt__VARIABLE__configTerm____prime
                          smt__CONSTANT__i__))
                      (and
                        (smt__TLA____IntLteq
                          (smt__TLA____FunApp
                            smt__VARIABLE__configVersion____prime
                            smt__CONSTANT__i__)
                          (smt__TLA____FunApp
                            smt__VARIABLE__configVersion____prime
                            smt__CONSTANT__j__))
                        (distinct
                          (smt__TLA____FunApp
                            smt__VARIABLE__configVersion____prime
                            smt__CONSTANT__i__)
                          (smt__TLA____FunApp
                            smt__VARIABLE__configVersion____prime
                            smt__CONSTANT__j__)))))
                  (and
                    (or
                      (and
                        (smt__TLA____IntLteq
                          (smt__TLA____FunApp
                            smt__VARIABLE__configTerm____prime
                            smt__CONSTANT__j__)
                          (smt__TLA____FunApp
                            smt__VARIABLE__configTerm____prime
                            smt__CONSTANT__i__))
                        (distinct
                          (smt__TLA____FunApp
                            smt__VARIABLE__configTerm____prime
                            smt__CONSTANT__j__)
                          (smt__TLA____FunApp
                            smt__VARIABLE__configTerm____prime
                            smt__CONSTANT__i__)))
                      (and
                        (=
                          (smt__TLA____FunApp
                            smt__VARIABLE__configTerm____prime
                            smt__CONSTANT__i__)
                          (smt__TLA____FunApp
                            smt__VARIABLE__configTerm____prime
                            smt__CONSTANT__j__))
                        (and
                          (smt__TLA____IntLteq
                            (smt__TLA____FunApp
                              smt__VARIABLE__configVersion____prime
                              smt__CONSTANT__j__)
                            (smt__TLA____FunApp
                              smt__VARIABLE__configVersion____prime
                              smt__CONSTANT__i__))
                          (distinct
                            (smt__TLA____FunApp
                              smt__VARIABLE__configVersion____prime
                              smt__CONSTANT__j__)
                            (smt__TLA____FunApp
                              smt__VARIABLE__configVersion____prime
                              smt__CONSTANT__i__))))) true)))))
          (forall ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
            (=>
              (and
                (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Server__)
                (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Server__))
              (or
                (not
                  (=
                    (smt__TLA____FunApp smt__VARIABLE__configTerm____prime
                      smt__CONSTANT__i__)
                    (smt__TLA____FunApp smt__VARIABLE__configTerm____prime
                      smt__CONSTANT__j__)))
                (or
                  (not
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__state____prime
                        smt__CONSTANT__i__) smt__CONSTANT__Primary__))
                  (and
                    (not
                      (or
                        (and
                          (smt__TLA____IntLteq
                            (smt__TLA____FunApp
                              smt__VARIABLE__configTerm____prime
                              smt__CONSTANT__i__)
                            (smt__TLA____FunApp
                              smt__VARIABLE__configTerm____prime
                              smt__CONSTANT__j__))
                          (distinct
                            (smt__TLA____FunApp
                              smt__VARIABLE__configTerm____prime
                              smt__CONSTANT__i__)
                            (smt__TLA____FunApp
                              smt__VARIABLE__configTerm____prime
                              smt__CONSTANT__j__)))
                        (and
                          (=
                            (smt__TLA____FunApp
                              smt__VARIABLE__configTerm____prime
                              smt__CONSTANT__j__)
                            (smt__TLA____FunApp
                              smt__VARIABLE__configTerm____prime
                              smt__CONSTANT__i__))
                          (and
                            (smt__TLA____IntLteq
                              (smt__TLA____FunApp
                                smt__VARIABLE__configVersion____prime
                                smt__CONSTANT__i__)
                              (smt__TLA____FunApp
                                smt__VARIABLE__configVersion____prime
                                smt__CONSTANT__j__))
                            (distinct
                              (smt__TLA____FunApp
                                smt__VARIABLE__configVersion____prime
                                smt__CONSTANT__i__)
                              (smt__TLA____FunApp
                                smt__VARIABLE__configVersion____prime
                                smt__CONSTANT__j__)))))) true)))))
          (forall ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
            (=>
              (and
                (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Server__)
                (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Server__))
              (forall ((smt__CONSTANT__Q__ Idv))
                (=>
                  (smt__TLA____Mem smt__CONSTANT__Q__
                    (smt__TLA____SetSt__flatnd__13
                      (smt__TLA____Subset
                        (smt__TLA____FunApp smt__VARIABLE__config____prime
                          smt__CONSTANT__j__)) smt__CONSTANT__j__))
                  (exists ((smt__CONSTANT__n__ Idv))
                    (and
                      (smt__TLA____Mem smt__CONSTANT__n__ smt__CONSTANT__Q__)
                      (or
                        (smt__TLA____IntLteq
                          (smt__TLA____FunApp
                            smt__VARIABLE__configTerm____prime
                            smt__CONSTANT__i__)
                          (smt__TLA____FunApp
                            smt__VARIABLE__currentTerm____prime
                            smt__CONSTANT__n__))
                        (forall ((smt__CONSTANT__Q___1 Idv))
                          (=>
                            (smt__TLA____Mem smt__CONSTANT__Q___1
                              (smt__TLA____SetSt__flatnd__13
                                (smt__TLA____Subset
                                  (smt__TLA____FunApp
                                    smt__VARIABLE__config____prime
                                    smt__CONSTANT__j__)) smt__CONSTANT__j__))
                            (exists ((smt__CONSTANT__n___1 Idv))
                              (and
                                (smt__TLA____Mem smt__CONSTANT__n___1
                                  smt__CONSTANT__Q___1)
                                (or
                                  (and
                                    (smt__TLA____IntLteq
                                      (smt__TLA____FunApp
                                        (smt__TLA____Tuple__2
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configVersion____prime
                                            smt__CONSTANT__j__)
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configTerm____prime
                                            smt__CONSTANT__j__))
                                        (smt__TLA____Cast__Int 2))
                                      (smt__TLA____FunApp
                                        (smt__TLA____Tuple__2
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configVersion____prime
                                            smt__CONSTANT__n___1)
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configTerm____prime
                                            smt__CONSTANT__n___1))
                                        (smt__TLA____Cast__Int 2)))
                                    (distinct
                                      (smt__TLA____FunApp
                                        (smt__TLA____Tuple__2
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configVersion____prime
                                            smt__CONSTANT__j__)
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configTerm____prime
                                            smt__CONSTANT__j__))
                                        (smt__TLA____Cast__Int 2))
                                      (smt__TLA____FunApp
                                        (smt__TLA____Tuple__2
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configVersion____prime
                                            smt__CONSTANT__n___1)
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configTerm____prime
                                            smt__CONSTANT__n___1))
                                        (smt__TLA____Cast__Int 2))))
                                  (and
                                    (=
                                      (smt__TLA____FunApp
                                        (smt__TLA____Tuple__2
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configVersion____prime
                                            smt__CONSTANT__n___1)
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configTerm____prime
                                            smt__CONSTANT__n___1))
                                        (smt__TLA____Cast__Int 2))
                                      (smt__TLA____FunApp
                                        (smt__TLA____Tuple__2
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configVersion____prime
                                            smt__CONSTANT__j__)
                                          (smt__TLA____FunApp
                                            smt__VARIABLE__configTerm____prime
                                            smt__CONSTANT__j__))
                                        (smt__TLA____Cast__Int 2)))
                                    (and
                                      (smt__TLA____IntLteq
                                        (smt__TLA____FunApp
                                          (smt__TLA____Tuple__2
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configVersion____prime
                                              smt__CONSTANT__j__)
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configTerm____prime
                                              smt__CONSTANT__j__))
                                          (smt__TLA____Cast__Int 1))
                                        (smt__TLA____FunApp
                                          (smt__TLA____Tuple__2
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configVersion____prime
                                              smt__CONSTANT__n___1)
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configTerm____prime
                                              smt__CONSTANT__n___1))
                                          (smt__TLA____Cast__Int 1)))
                                      (distinct
                                        (smt__TLA____FunApp
                                          (smt__TLA____Tuple__2
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configVersion____prime
                                              smt__CONSTANT__j__)
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configTerm____prime
                                              smt__CONSTANT__j__))
                                          (smt__TLA____Cast__Int 1))
                                        (smt__TLA____FunApp
                                          (smt__TLA____Tuple__2
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configVersion____prime
                                              smt__CONSTANT__n___1)
                                            (smt__TLA____FunApp
                                              smt__VARIABLE__configTerm____prime
                                              smt__CONSTANT__n___1))
                                          (smt__TLA____Cast__Int 1)))))))))))))))))
          (forall ((smt__CONSTANT__i__ Idv) (smt__CONSTANT__j__ Idv))
            (=>
              (and
                (smt__TLA____Mem smt__CONSTANT__i__ smt__CONSTANT__Server__)
                (smt__TLA____Mem smt__CONSTANT__j__ smt__CONSTANT__Server__))
              (or
                (=
                  (smt__TLA____FunApp smt__VARIABLE__configTerm____prime
                    smt__CONSTANT__j__)
                  (smt__TLA____FunApp smt__VARIABLE__currentTerm____prime
                    smt__CONSTANT__j__))
                (and
                  (not
                    (=
                      (smt__TLA____FunApp smt__VARIABLE__state____prime
                        smt__CONSTANT__j__) smt__CONSTANT__Primary__)) 
                  true))))))) :named |Goal|))

(check-sat)
(exit)
