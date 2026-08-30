---------------------------- MODULE cbc_max ----------------------------
EXTENDS Integers, FiniteSets, TLC

(* An encoding of the conditional consensus protocol based on the maximal value
   which is proposed by processes.  See Mostéfaoui, Achour, et al., DSN 2003.
   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016; patched in 2024 to fix a
   lost-update bug in the Receive action (a message that could not yet be used
   is now left pending instead of being consumed and discarded). *)

CONSTANT N, F, T, Values, Bottom

ASSUME 2 * T < N /\ 0 <= F /\ F <= T /\ 0 < N
ASSUME \A v \in Values: v # Bottom

VARIABLES pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs
vars == << pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

Proc == 1..N
Status == { "BCAST1", "PHS1", "PREP","BCAST2", "PHS2", "DONE", "CRASH", "CHOOSE" }

Msg1s == [ type: {"Phs1"} , value: Values, sndr: Proc ]
Msg2s == [ type: {"Phs2"}, value: Values, wValue: Values, sndr: Proc ]
Msgs == Msg1s \cup Msg2s

Phs1Msg(v_i, i) == [ type |-> "Phs1", value |-> v_i, sndr |-> i ]
Phs2Msg(v_i, w_i, i) == [ type |-> "Phs2", value |-> v_i, wValue |-> w_i, sndr |-> i ]

MAX(arr) == CHOOSE maxVal \in Values: /\ (\E p \in Proc: arr[p] = maxVal)
                                       /\ (\A p \in Proc: maxVal >= arr[p])

Init ==
  /\ V = [ i \in Proc |-> [ j \in Proc |-> Bottom ] ]
  /\ v \in [ Proc -> Values ]
  /\ pc = [ i \in Proc |-> "BCAST1" ]
  /\ w = [ i \in Proc |-> Bottom ]
  /\ dval = [ i \in Proc |-> Bottom ]
  /\ nCrash = 0
  /\ sntMsgs = {}
  /\ rcvdMsgs = [ i \in Proc |-> {} ]

Crash(i) ==
  /\ nCrash < F
  /\ pc[i] # "CRASH"
  /\ nCrash' = nCrash + 1
  /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
  /\ UNCHANGED << V, w, dval, v, sntMsgs, rcvdMsgs >>

(* A message is only consumed when it matches the recipient's phase; otherwise
   it stays pending so it can be received once the recipient catches up. *)
Receive(i) ==
  \E msg \in Msgs :
    /\ pc[i] # "CRASH"
    /\ \/ /\ pc[i] = "PHS1" /\ msg.type = "Phs1"
         \/ /\ pc[i] = "PHS2" /\ msg.type = "Phs2"
    /\ msg \in sntMsgs
    /\ msg \notin rcvdMsgs[i]
    /\ rcvdMsgs' = [ rcvdMsgs EXCEPT ![i] = rcvdMsgs[i] \cup { msg } ]
    /\ LET j == msg.sndr IN V' = [ V EXCEPT ![i][j] = msg.value ]
    /\ UNCHANGED << pc, v, w, dval, nCrash, sntMsgs >>

BcastPhs1(i) ==
  /\ pc[i] = "BCAST1"
  /\ pc' = [ pc EXCEPT ![i] = "PHS1" ]
  /\ sntMsgs' = sntMsgs \cup { Phs1Msg(v[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

Phs1(i) ==
  /\ pc[i] = "PHS1"
  /\ pc' = [ pc EXCEPT ![i] = "BCAST2" ]
  /\ Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs1" }) >= N - T
  /\ w' = [ w EXCEPT ![i] = MAX(V[i]) ]
  /\ UNCHANGED << v, dval, nCrash, sntMsgs, rcvdMsgs, V >>

BcastPhs2(i) ==
  /\ pc[i] = "BCAST2"
  /\ pc' = [ pc EXCEPT ![i] = "PHS2" ]
  /\ sntMsgs' = sntMsgs \cup { Phs2Msg(v[i], w[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

(* The quorum-decision takes strict priority; the deterministic fallback is
   reachable only when no value has a quorum among all PHASE2 echoes. *)
Phs2(i) ==
  /\ pc[i] = "PHS2"
  /\ \/ \E v0 \in Values:
            /\ Cardinality( { m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.wValue = v0 } )  >= N - T
            /\ dval' = [ dval EXCEPT ![i] = v0 ]
            /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
            /\ UNCHANGED << v, w, nCrash, sntMsgs, rcvdMsgs, V >>
     \/ /\ \A j \in Proc: \E m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.sndr = j
        /\ \A v0 \in Values:
             Cardinality( { m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.wValue = v0 } ) < N - T
        /\ pc' = [ pc EXCEPT ![i] = "CHOOSE"]
        /\ UNCHANGED << v, w, nCrash, sntMsgs, dval, rcvdMsgs, V >>

Choose(i) ==
  /\ pc[i] = "CHOOSE"
  /\ dval' = [ dval EXCEPT ![i] = (CHOOSE tV \in Values: (\E j \in Proc: tV = V[i][j])) ]
  /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
  /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>

Next == \E i \in Proc: \/ Crash(i)
                       \/ Receive(i)
                       \/ BcastPhs1(i)
                       \/ Phs1(i)
                       \/ BcastPhs2(i)
                       \/ Phs2(i)
                       \/ Choose(i)
                       \/ /\ \A p \in Proc : pc[p] = "CRASH" \/ pc[p] = "DONE"
                          /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
       /\ WF_vars(\E i \in Proc: \/ Receive(i)
                                 \/ BcastPhs1(i)
                                 \/ Phs1(i)
                                 \/ BcastPhs2(i)
                                 \/ Phs2(i)
                                 \/ Choose(i))

Agreement == \A i, j \in Proc: (dval[i] # Bottom \/ dval[j] # Bottom) => dval[i] = dval[j]
=============================================================================