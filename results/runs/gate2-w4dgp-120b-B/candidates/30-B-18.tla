---- MODULE cbc_max ----
(* Conditional consensus: the pipelined, majority-rule version driven by the
   condition C1 = "at least F+1 processes propose the maximal value". See Mostefaoui,
   Achour, et al. "Evaluating the condition-based approach to solve consensus." DSN
   2003; this is the version with the fallback deterministic choice. *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS N, F, T, Values, Bottom

ASSUME 2 * T < N /\ 0 <= F /\ F <= T /\ 0 < N /\ \A v \in Values: v # Bottom

VARIABLES pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs

vars == << pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

Proc   == 1..N
Status == { "BCAST1","PHS1","PREP","BCAST2","PHS2","DONE","CRASH","CHOOSE" }

Msg1s == [ type : {"Phs1"} , value : Values, sndr : Proc ]
Msg2s == [ type : {"Phs2"}, value : Values, wValue : Values, sndr : Proc ]
Msgs  == Msg1s \cup Msg2s

Phs1Msg(v,i) == [ type |-> "Phs1", value |-> v, sndr |-> i ]
Phs2Msg(v,w,i) == [ type |-> "Phs2", value |-> v, wValue |-> w, sndr |-> i ]

MAX(arr) == CHOOSE m \in Values : /\ (\E p \in Proc: arr[p] = m)
                              /\ (\A p \in Proc: m >= arr[p])

Init ==
  /\ V = [ i \in Proc |-> [ j \in Proc |-> Bottom ] ]
  /\ v \in [ Proc -> Values ]
  /\ pc = [ i \in Proc |-> "BCAST1" ]
  /\ w = [ i \in Proc |-> Bottom ]
  /\ dval = [ i \in Proc |-> Bottom ]
  /\ nCrash = 0
  /\ sntMsgs = {}
  /\ rcvdMsgs = [ i \in Proc |-> {} ]

(* A process may crash early, before it takes any step. *)
Crash(i) ==
  /\ nCrash < F
  /\ pc[i] # "CRASH"
  /\ nCrash' = nCrash + 1
  /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
  /\ UNCHANGED << V, v, w, dval, sntMsgs, rcvdMsgs >>

(* Receiving is guarded by a matching phase: a Phase2 message that arrives too
   early for its recipient stays pending instead of being silently dropped. *)
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

(* Phase1: taking a maximal proposal from the Phase1 messages the process has seen. *)
Phs1(i) ==
  /\ pc[i] = "PHS1"
  /\ pc' = [ pc EXCEPT ![i] = "BCAST2" ]
  /\ Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs1" }) >= N - T
  /\ w' = [ w EXCEPT ![i] = MAX(V[i]) ]
  /\ UNCHANGED << V, v, dval, nCrash, sntMsgs, rcvdMsgs >>

BcastPhs2(i) ==
  /\ pc[i] = "BCAST2"
  /\ pc' = [ pc EXCEPT ![i] = "PHS2" ]
  /\ sntMsgs' = sntMsgs \cup { Phs2Msg(v[i], w[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

(* Phase2: a quorum on the echoed value decides it; only when no value has a
   quorum among PHASE2 echoes does the deterministic fallback return(F(Y_i)). *)
Phs2(i) ==
  /\ pc[i] = "PHS2"
  /\ \/ \E v0 \in Values :
        /\ Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.wValue = v0 }) >= N - T
        /\ dval' = [ dval EXCEPT ![i] = v0 ]
        /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
        /\ UNCHANGED << v, w, nCrash, sntMsgs, rcvdMsgs, V >>
     \/ /\ \A j \in Proc : \E m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.sndr = j
        /\ \A v0 \in Values :
             Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.wValue = v0 }) < N - T
        /\ pc' = [ pc EXCEPT ![i] = "CHOOSE" ]
        /\ UNCHANGED << v, w, dval, nCrash, sntMsgs, rcvdMsgs, V >>

(* Deterministic fallback when no quorum is available: the condition requires a
   full input, so at most one value can still be in V[i] in that case. *)
Choose(i) ==
  /\ pc[i] = "CHOOSE"
  /\ dval' = [ dval EXCEPT ![i] = (CHOOSE t \in Values : \E j \in Proc : t = V[i][j]) ]
  /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
  /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>

Next == \E i \in Proc :
  \/ Crash(i) \/ Receive(i) \/ BcastPhs1(i) \/ Phs1(i) \/ BcastPhs2(i) \/ Phs2(i)
  \/ Choose(i)
  \/ /\ \A p \in Proc : pc[p] \in {"CRASH","DONE"} /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E i \in Proc : Receive(i) \/ BcastPhs1(i) \/ Phs1(i)
                                   \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i))

TypeOK ==
  /\ V \in [ Proc -> [ Proc -> Values \cup {Bottom} ] ]
  /\ v \in [ Proc -> Values ]
  /\ pc \in [ Proc -> Status ]
  /\ w \in [ Proc -> Values \cup {Bottom} ]
  /\ dval \in [ Proc -> Values \cup {Bottom} ]
  /\ nCrash \in 0..F
  /\ sntMsgs \in SUBSET Msgs
  /\ rcvdMsgs \in [ Proc -> SUBSET Msgs ]

(* Any decided value was actually proposed. *)
Validity == \A i \in Proc : dval[i] # Bottom => \E j \in Proc : dval[i] = v[j]

(* No two processes decide differently. *)
Agreement == \A i, j \in Proc : (dval[i] # Bottom \/ dval[j] # Bottom) => dval[i] = dval[j]

(* Every correct process eventually decides. *)
Termination == <>(\A i \in Proc : pc[i] \in {"CRASH","DONE"})

(* At least F+1 processes propose the greatest value. *)
Condition1 == Cardinality({ j \in Proc : v[j] = MAX(v) }) > F

(* The condition is sufficient: it forces termination of the correct branch. *)
RealTermination == Condition1 => Termination

====