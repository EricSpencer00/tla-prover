---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets, TLC

CONSTANT N, F, T, Values, Bottom

ASSUME 2 * T < N /\ 0 <= F /\ F <= T /\ 0 < N
ASSUME \A v \in Values: v # Bottom

VARIABLES pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs

vars == << pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

Proc == 1..N

Status == { "BCAST1", "PHS1", "PREP","BCAST2", "PHS2", "DONE", "CRASH", "CHOOSE" }

(* Create a new message *)
Phs1Msg(v_i, i) == [ type |-> "Phs1", value |-> v_i, sndr |-> i ]
Phs2Msg(v_i, w_i, i) == [ type |-> "Phs2", value |-> v_i,
                          wValue |-> w_i, sndr |-> i ]

(* A line of PHASE2 messages broadcast for each process *)
Msg1s == [ type : {"Phs1"}, value : Values, sndr : Proc ]
Msg2s == [ type : {"Phs2"}, value : Values, wValue : Values, sndr : Proc ]
Msgs  == Msg1s \cup Msg2s

(* Find the maximum value in an array of values *)
MAX(arr) == CHOOSE max \in Values : /\ (\E p \in Proc: arr[p] = max)
                                 /\ (\A p \in Proc: max >= arr[p])

(* Line 1 of the protocol *)
Init ==
  /\ V = [ i \in Proc |-> [ j \in Proc |-> Bottom ] ]
  /\ v \in [ Proc -> Values ]
  /\ pc = [ i \in Proc |-> "BCAST1" ]
  /\ w = [ i \in Proc |-> Bottom ]
  /\ dval = [ i \in Proc |-> Bottom ]
  /\ nCrash = 0
  /\ sntMsgs = {}
  /\ rcvdMsgs = [ i \in Proc |-> {} ]

(* If there is room for another fault, a process may crash *)
Crash(i) ==
  /\ nCrash < F
  /\ pc[i] # "CRASH"
  /\ nCrash' = nCrash + 1
  /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
  /\ UNCHANGED << V, w, dval, v, sntMsgs, rcvdMsgs >>

(* Receive a message that has not yet been consumed, only if it is usable in the
   current phase; otherwise it stays pending for a later Receive (its sender has
   not reached the matching phase yet) instead of being permanently dropped. *)
Receive(i) ==
  \E msg \in Msgs :
    /\ pc[i] # "CRASH"
    /\ \/ /\ pc[i] = "PHS1"
          /\ msg.type = "Phs1"
       \/ /\ pc[i] = "PHS2"
          /\ msg.type = "Phs2"
    /\ msg \in sntMsgs
    /\ msg \notin rcvdMsgs[i]
    /\ rcvdMsgs' = [ rcvdMsgs EXCEPT ![i] = rcvdMsgs[i] \cup {msg} ]
    /\ V' = [ V EXCEPT ![i][msg.sndr] = msg.value ]
    /\ UNCHANGED << pc, v, w, dval, nCrash, sntMsgs >>

(* Broadcast PHASE1(v_i, i) *)
BcastPhs1(i) ==
  /\ pc[i] = "BCAST1"
  /\ pc' = [ pc EXCEPT ![i] = "PHS1" ]
  /\ sntMsgs' = sntMsgs \cup { Phs1Msg(v[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

(* A process in PHASE1 that has collected at least N-T PHASE1 messages takes an
   estimation and moves to PHASE2. *)
Phs1(i) ==
  /\ pc[i] = "PHS1"
  /\ Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs1" }) >= N - T
  /\ w' = [ w EXCEPT ![i] = MAX(V[i]) ]
  /\ pc' = [ pc EXCEPT ![i] = "BCAST2" ]
  /\ UNCHANGED << V, v, dval, nCrash, sntMsgs, rcvdMsgs >>

(* Broadcast PHASE2(v_i, w_i, i) for the same estimation *)
BcastPhs2(i) ==
  /\ pc[i] = "BCAST2"
  /\ pc' = [ pc EXCEPT ![i] = "PHS2" ]
  /\ sntMsgs' = sntMsgs \cup { Phs2Msg(v[i], w[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

(* Decide by quorum on the second phase if one exists; otherwise advance to the
   deterministic fallback CHOOSE branch, which is reachable only when no value
   ever reaches a quorum among all N PHASE2 echoes -- this is what prevents a
   disagreement with the guarded majority-decision path. *)
Phs2(i) ==
  /\ pc[i] = "PHS2"
  /\ \/ \E v0 \in Values:
        /\ Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.wValue = v0 })
           >= N - T
        /\ dval' = [ dval EXCEPT ![i] = v0 ]
        /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
        /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>
     \/ /\ \A j \in Proc : \E m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.sndr = j
        /\ \A v0 \in Values:
             Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.wValue = v0 })
               < N - T
        /\ pc' = [ pc EXCEPT ![i] = "CHOOSE" ]
        /\ UNCHANGED << V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

(* Having collected all PHASE2 messages, a process deterministically chooses a
   value it has actually seen in its own view of the world. *)
Choose(i) ==
  /\ pc[i] = "CHOOSE"
  /\ dval' = [ dval EXCEPT ![i] =
                 (CHOOSE tV \in Values : \E j \in Proc : tV = V[i][j]) ]
  /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
  /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>

Next == \E i \in Proc : Crash(i) \/ Receive(i) \/ BcastPhs1(i) \/ Phs1(i)
                         \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i)
                         \/ /\ \A p \in Proc : pc[p] \in {"CRASH", "DONE"}
                            /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E i \in Proc : Receive(i) \/ BcastPhs1(i) \/ Phs1(i)
                                 \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i))

TypeOK ==
  /\ V \in [ Proc -> [ Proc -> { Bottom } \cup Values ] ]
  /\ v \in [ Proc -> Values ]
  /\ pc \in [ Proc -> Status ]
  /\ w \in [ Proc -> { Bottom } \cup Values ]
  /\ dval \in [ Proc -> { Bottom } \cup Values ]
  /\ nCrash \in 0 .. F
  /\ sntMsgs \in SUBSET Msgs
  /\ rcvdMsgs \in [ Proc -> SUBSET Msgs ]

(* If a process decides on v, then v was proposed by some process. *)
Validity == \A i \in Proc : dval[i] # Bottom => \E j \in Proc : dval[i] = v[j]

(* No two processes ever decide on different values. *)
Agreement == \A i, j \in Proc : (dval[i] # Bottom \/ dval[j] # Bottom)
                              => dval[i] = dval[j]

(* Every correct process eventually decides on something. *)
Termination == <>(\A i \in Proc : pc[i] \in {"CRASH", "DONE"})

(* The condition that triggers termination: over F processes start with the
   greatest value in the input vector. *)
Condition1 == Cardinality({ j \in Proc : v[j] = MAX(v) }) > F

(* If the condition is satisfied, the algorithm makes progress and terminates. *)
RealTermination == Condition1 => Termination

=============================================================================