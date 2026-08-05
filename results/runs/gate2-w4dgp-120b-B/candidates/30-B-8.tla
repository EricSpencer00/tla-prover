---- MODULE cbc_max ------------------------------------------------------------
(* An encoding of the conditional consensus protocol based on the maximal value
   which is proposed by processes. This protocol is described in Fig. 1 with
   condition C1 in Mostéfaoui, Achour, et al., "Evaluating the condition-based
   approach to solve consensus," DSN'03.

   The original spec had three defects: (1) V was listed in UNCHANGED on the same
   action line that assigned it in a LET, so V' was silently forced back to V;
   (2) a message could be dropped by Receive: ANY sent, not-yet-received message
   was marked received unconditionally, but V only updated when pc[i] matched the
   message phase, so a message that arrived too early silently vanished forever
   from V; (3) Phs2's two decision branches were unguarded, so a quorum-decider
   and a fallback chooser could disagree. Fixes: (1) scatter the UNCHANGEDs;
   (2) Move the phase/type match from the inner IF into the action's enablement
   so a message that cannot yet be used stays pending rather than being consumed;
   (3) Guard the fallback CHOOSE branch with "no value has a quorum among PHASE2
   echoes".
 *)
EXTENDS Integers, FiniteSets

CONSTANTS N, F, T, Values, Bottom

ASSUME 2 * T < N /\ 0 <= F /\ F <= T /\ 0 < N
ASSUME \A v \in Values : v # Bottom

VARIABLES pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs

vars == << pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

Proc == 1..N
Status == { "BCAST1", "PHS1", "PREP","BCAST2", "PHS2",
            "DONE", "CRASH", "CHOOSE" }
Msg1s == [ type : {"Phs1"}, value : Values, sndr : Proc ]
Msg2s == [ type : {"Phs2"}, value : Values, wValue : Values, sndr : Proc ]
Msgs == Msg1s \cup Msg2s

Phs1Msg(v,i) == [ type |-> "Phs1", value |-> v, sndr |-> i ]
Phs2Msg(v,w,i) == [ type |-> "Phs2", value |-> v, wValue |-> w, sndr |-> i ]

(* Find the maximum value in arr *)
MAX(arr) == CHOOSE max \in Values :
  /\ (\E p \in Proc : arr[p] = max)
  /\ (\A p \in Proc : max >= arr[p])

Init ==
  /\ V = [ i \in Proc |-> [ j \in Proc |-> Bottom ] ]
  /\ v \in [ Proc -> Values ]
  /\ pc = [ i \in Proc |-> "BCAST1" ]
  /\ w = [ i \in Proc |-> Bottom ]
  /\ dval = [ i \in Proc |-> Bottom ]
  /\ nCrash = 0
  /\ sntMsgs = {}
  /\ rcvdMsgs = [ i \in Proc |-> {} ]

(* If there are less than F faulty processes, process i becomes faulty. *)
Crash(i) ==
  /\ nCrash < F
  /\ pc[i] # "CRASH"
  /\ nCrash' = nCrash + 1
  /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
  /\ UNCHANGED << V, w, dval, v, sntMsgs, rcvdMsgs >>

(* Receives a new message (phase match is in the enablement) *)
Receive(i) ==
  \E msg \in Msgs :
    /\ pc[i] # "CRASH"
    /\ \/ /\ pc[i] = "PHS1" /\ msg.type = "Phs1"
          \/ /\ pc[i] = "PHS2" /\ msg.type = "Phs2"
    /\ msg \in sntMsgs /\ msg \notin rcvdMsgs[i]
    /\ rcvdMsgs' = [ rcvdMsgs EXCEPT ![i] = rcvdMsgs[i] \cup { msg } ]
    /\ LET j == msg.sndr
       IN V' = [ V EXCEPT ![i][j] = msg.value ]
    /\ UNCHANGED << pc, v, w, dval, nCrash, sntMsgs >>

(* Broadcast PHASE1(v_i, i) *)
BcastPhs1(i) ==
  /\ pc[i] = "BCAST1"
  /\ pc' = [ pc EXCEPT ![i] = "PHS1" ]
  /\ sntMsgs' = sntMsgs \cup { Phs1Msg(v[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

(* If a process received PHASE1(_, _) from at least N - F processes, it updates
   its view and makes an estimation. *)
Phs1(i) ==
  /\ pc[i] = "PHS1"
  /\ pc' = [ pc EXCEPT ![i] = "BCAST2" ]
  /\ Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs1" }) >= N - T
  /\ w' = [ w EXCEPT ![i] = MAX(V[i]) ]
  /\ UNCHANGED << V, v, dval, nCrash, sntMsgs, rcvdMsgs >>

(* Broadcast the estimated value. *)
BcastPhs2(i) ==
  /\ pc[i] = "BCAST2"
  /\ pc' = [ pc EXCEPT ![i] = "PHS2" ]
  /\ sntMsgs' = sntMsgs \cup { Phs2Msg(v[i], w[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

(* Receives a new PHASE2: either decides on a quorum value or, if none exists,
   moves to the CHOOSE step (taken after every delivery, so the fallback fires
   only when the quorum rule never applied, i.e. no value gathers a quorum). *)
Phs2(i) ==
  /\ pc[i] = "PHS2"
  /\ \/ /\ \E v0 \in Values:
        /\ Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.wValue = v0 }) >= N - T
        /\ dval' = [ dval EXCEPT ![i] = v0 ]
        /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
        /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>
     \/ /\ \A j \in Proc : \E m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.sndr = j
        /\ \A v0 \in Values :
             Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.wValue = v0 }) < N - T
        /\ pc' = [ pc EXCEPT ![i] = "CHOOSE" ]
        /\ UNCHANGED << V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

(* Having received all PHASE2 messages, a process deterministically chooses a
   value appearing in V[i]. *)
Choose(i) ==
  /\ pc[i] = "CHOOSE"
  /\ dval' = [ dval EXCEPT ![i] = CHOOSE tV \in Values : \E j \in Proc : tV = V[i][j] ]
  /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
  /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>

Next == \E i \in Proc :
  \/ Crash(i) \/ Receive(i) \/ BcastPhs1(i) \/ Phs1(i)
  \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i)
  \/ /\ \A p \in Proc : pc[p] \in {"CRASH","DONE"} /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
       /\ WF_vars(\E i \in Proc : Receive(i) \/ BcastPhs1(i) \/ Phs1(i)
                                 \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i))

TypeOK ==
  /\ V \in [ Proc -> [ Proc -> Values \cup {Bottom} ] ]
  /\ v \in [ Proc -> Values ] /\ w \in [ Proc -> Values \cup {Bottom} ]
  /\ dval \in [ Proc -> Values \cup {Bottom} ]
  /\ pc \in [ Proc -> Status ] /\ nCrash \in 0..F
  /\ sntMsgs \in SUBSET Msgs
  /\ rcvdMsgs \in [ Proc -> SUBSET Msgs ]

(* If a process decides v, v was proposed by some process. *)
Validity == \A i \in Proc : dval[i] # Bottom => (\E j \in Proc : dval[i] = v[j])

(* No two processes decide differently. *)
Agreement == \A i, j \in Proc : (dval[i] # Bottom \/ dval[j] # Bottom) => dval[i] = dval[j]

(* Every correct process eventually decides. *)
Termination == <>(\A i \in Proc : pc[i] \in {"CRASH","DONE"})

(* At least F + 1 processes start with the greatest value. *)
Condition1 == Cardinality({ j \in Proc : v[j] = MAX(v) }) > F

(* The algorithm terminates when the input satisfies Condition1. *)
RealTermination == Condition1 => Termination

=============================================================================