---- MODULE cbc_max ----
\* An encoding of the conditional consensus protocol based on the maximal value
\* that is proposed by processes.  The protocol is described in Fig. 1 (condition
\* C1) of Mostéfaoui, Achour, et al., DSN 2003.  The original JACM (2013) source
\* was patched (this file) for two unrelated bugs that surfaced as live TLC
\* counterexamples: (1) a line that listed V in UNCHANGED on the same action
\* that LET-assigned V' silently reverted the assignment, and (2) a PHASE2
\* receive that silently dropped a message it could not yet use, so it could never
\* be re-received later.  Neither patch weakens any invariant.
EXTENDS Integers, FiniteSets, TLC

CONSTANT N, F, T, Values, Bottom

ASSUME 2 * T < N /\ 0 <= F /\ F <= T /\ 0 < N
ASSUME \A v \in Values: v # Bottom

VARIABLES pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs
vars == << pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

Proc == 1..N
Status == { "BCAST1", "PHS1", "PREP","BCAST2", "PHS2", "DONE", "CRASH", "CHOOSE" }

(* Create a new message. *)
Phs1Msg(v_i, i) == [ type |-> "Phs1", value |-> v_i, sndr |-> i ]
Phs2Msg(v_i, w_i, i) == [ type |-> "Phs2", value |-> v_i, wValue |-> w_i, sndr |-> i ]

Msgs == [ type: {"Phs1","Phs2"}, value: Values, sndr: Proc, wValue: Values ]

(* Find the maximum value in arr. *)
MAX(arr) == CHOOSE max \in Values: /\ (\E p \in Proc: arr[p] = max)
                                   /\ (\A p \in Proc: max >= arr[p])

Init ==
  /\ V = [ i \in Proc |-> [ j \in Proc |-> Bottom ] ]
  /\ v \in [ Proc -> Values ]
  /\ pc = [ i \in Proc |-> "BCAST1" ]
  /\ w = [ i \in Proc |-> Bottom ]
  /\ dval = [ i \in Proc |-> Bottom ]
  /\ nCrash = 0
  /\ sntMsgs = {}
  /\ rcvdMsgs = [ i \in Proc |-> {} ]

(* If there are fewer than F faulty processes, process i crashes. *)
Crash(i) ==
  /\ nCrash < F
  /\ pc[i] # "CRASH"
  /\ nCrash' = nCrash + 1
  /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
  /\ UNCHANGED << V, w, dval, v, sntMsgs, rcvdMsgs >>

(* Receives a new message, but only one whose phase matches pc[i]; a message
   that has arrived too early stays pending instead of being silently dropped. *)
Receive(i) ==
  \E msg \in Msgs:
    /\ pc[i] # "CRASH"
    /\ pc[i] = "PHS1" => msg.type = "Phs1"
    /\ pc[i] = "PHS2" => msg.type = "Phs2"
    /\ msg \in sntMsgs
    /\ msg \notin rcvdMsgs[i]
    /\ rcvdMsgs' = [ rcvdMsgs EXCEPT ![i] = rcvdMsgs[i] \cup { msg } ]
    /\ LET j == msg.sndr IN V' = [ V EXCEPT ![i][j] = msg.value ]
    /\ UNCHANGED << pc, v, w, dval, nCrash, sntMsgs >>

(* Broadcasts PHASE1(v_i, i). *)
BcastPhs1(i) ==
  /\ pc[i] = "BCAST1"
  /\ pc' = [ pc EXCEPT ![i] = "PHS1" ]
  /\ sntMsgs' = sntMsgs \cup { Phs1Msg(v[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

(* Objecting to at least N - F Phase1 messages: update the estimate. *)
Phs1(i) ==
  /\ pc[i] = "PHS1"
  /\ Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs1" }) >= N - T
  /\ pc' = [ pc EXCEPT ![i] = "BCAST2" ]
  /\ w' = [ w EXCEPT ![i] = MAX(V[i]) ]
  /\ UNCHANGED << V, v, dval, nCrash, sntMsgs, rcvdMsgs >>

(* Broadcasts PHASE2. *)
BcastPhs2(i) ==
  /\ pc[i] = "BCAST2"
  /\ pc' = [ pc EXCEPT ![i] = "PHS2" ]
  /\ sntMsgs' = sntMsgs \cup { Phs2Msg(v[i], w[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

(* Deliver Phase2: decide on a quorum value, or move to CHOOSE if none exists. *)
Phs2(i) ==
  /\ pc[i] = "PHS2"
  /\ \/ \E v0 \in Values:
         /\ Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.wValue = v0 }) >= N - T
         /\ dval' = [ dval EXCEPT ![i] = v0 ]
         /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
         /\ UNCHANGED << v, w, nCrash, sntMsgs, rcvdMsgs, V >>
     \/ /\ \A j \in Proc: \E m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.sndr = j
        /\ \A v0 \in Values:
             Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.wValue = v0 }) < N - T
        /\ pc' = [ pc EXCEPT ![i] = "CHOOSE" ]
        /\ UNCHANGED << v, w, dval, nCrash, sntMsgs, rcvdMsgs, V >>

(* All PHASE2 messages are in, so choose a witnessed value from V[i]. *)
Choose(i) ==
  /\ pc[i] = "CHOOSE"
  /\ dval' = [ dval EXCEPT ![i] = (CHOOSE tV \in Values: \E j \in Proc: tV = V[i][j]) ]
  /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
  /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>

Next == \E i \in Proc: \/ Crash(i) \/ Receive(i) \/ BcastPhs1(i)
                       \/ Phs1(i) \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i)
                       \/ /\ \A p \in Proc: pc[p] \in {"CRASH","DONE"}
                          /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E i \in Proc: Receive(i) \/ BcastPhs1(i) \/ Phs1(i)
                                  \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i))

TypeOK ==
  /\ V \in [ Proc -> [ Proc -> {Bottom} \cup Values ] ]
  /\ v \in [ Proc -> Values ]
  /\ pc \in [ Proc -> Status ]
  /\ w \in [ Proc -> {Bottom} \cup Values ]
  /\ dval \in [ Proc -> {Bottom} \cup Values ]
  /\ nCrash \in 0 .. F
  /\ sntMsgs \in SUBSET Msgs
  /\ rcvdMsgs \in [ Proc -> SUBSET Msgs ]

(* A decision must be a value that was actually proposed. *)
Validity == \A i \in Proc: dval[i] # Bottom => \E j \in Proc: dval[i] = v[j]

(* No two processes decide differently. *)
Agreement == \A i, j \in Proc: (dval[i] # Bottom \/ dval[j] # Bottom) => dval[i] = dval[j]

(* Every correct process eventually decides. *)
Termination == <>(\A i \in Proc: pc[i] \in {"CRASH","DONE"})

(* At least F + 1 processes propose the greatest value. *)
Condition1 == Cardinality({ j \in Proc: v[j] = MAX(v) }) > F

(* The protocol terminates whenever Condition1 holds. *)
RealTermination == Condition1 => Termination

====