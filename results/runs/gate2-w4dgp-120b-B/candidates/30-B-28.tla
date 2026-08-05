---- MODULE cbc_max
EXTENDS Integers, FiniteSets, TLC

CONSTANT N, F, T, Values, Bottom

ASSUME 2 * T < N /\ 0 <= F /\ F <= T /\ 0 < N
ASSUME \A v \in Values: v # Bottom

VARIABLES pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs
vars == << pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

Phs1Msg(v_i, i) == [ type |-> "Phs1", value |-> v_i, sndr |-> i ]
Phs2Msg(v_i, w_i, i) == [ type |-> "Phs2", value |-> v_i, wValue |-> w_i, sndr |-> i ]

Msg1s == [ type : {"Phs1"}, value : Values, sndr : 1..N ]
Msg2s == [ type : {"Phs2"}, value : Values, wValue : Values, sndr : 1..N ]
Msgs == Msg1s \cup Msg2s

MAX(arr) == CHOOSE maxVal \in Values: /\ (\E p \in 1..N: arr[p] = maxVal)
                                       /\ (\A p \in 1..N: maxVal >= arr[p])

Init ==
  /\ V = [ i \in 1..N |-> [ j \in 1..N |-> Bottom ] ]
  /\ v \in [ 1..N -> Values ]
  /\ pc = [ i \in 1..N |-> "BCAST1" ]
  /\ w = [ i \in 1..N |-> Bottom ]
  /\ dval = [ i \in 1..N |-> Bottom ]
  /\ nCrash = 0
  /\ sntMsgs = {}
  /\ rcvdMsgs = [ i \in 1..N |-> {} ]

Crash(i) ==
  /\ nCrash < F
  /\ pc[i] \notin {"CRASH", "DONE"}
  /\ nCrash' = nCrash + 1
  /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
  /\ UNCHANGED << V, w, dval, v, sntMsgs, rcvdMsgs >>

(* A message is only received if its type matches this process's current phase;
   otherwise it is not delivered this step and remains pending, since taking it
   unconditionally would silently drop it and break eventual agreement. *)
Receive(i) ==
  \E msg \in Msgs :
    /\ pc[i] # "CRASH"
    /\ \/ /\ pc[i] = "PHS1" /\ msg.type = "Phs1"
         \/ /\ pc[i] = "PHS2" /\ msg.type = "Phs2"
    /\ msg \in sntMsgs
    /\ msg \notin rcvdMsgs[i]
    /\ LET j == msg.sndr IN
         V' = [ V EXCEPT ![i][j] = msg.value ]
    /\ rcvdMsgs' = [ rcvdMsgs EXCEPT ![i] = rcvdMsgs[i] \cup { msg } ]
    /\ UNCHANGED << pc, v, w, dval, nCrash, sntMsgs >>

BcastPhs1(i) ==
  /\ pc[i] = "BCAST1"
  /\ pc' = [ pc EXCEPT ![i] = "PHS1" ]
  /\ sntMsgs' = sntMsgs \cup { Phs1Msg(v[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

Phs1(i) ==
  /\ pc[i] = "PHS1"
  /\ Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs1" }) >= N - T
  /\ pc' = [ pc EXCEPT ![i] = "BCAST2" ]
  /\ w' = [ w EXCEPT ![i] = MAX(V[i]) ]
  /\ UNCHANGED << V, v, dval, nCrash, sntMsgs, rcvdMsgs >>

BcastPhs2(i) ==
  /\ pc[i] = "BCAST2"
  /\ pc' = [ pc EXCEPT ![i] = "PHS2" ]
  /\ sntMsgs' = sntMsgs \cup { Phs2Msg(v[i], w[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

(* A quorum decision on a value always runs before the deterministic fallback;
   the disjunction is guarded so the fallback is only reachable when no value
   has a quorum among the PHASE2 echoes. *)
Phs2(i) ==
  /\ pc[i] = "PHS2"
  /\ \/ \E v0 \in Values :
        /\ Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.wValue = v0 }) >= N - T
        /\ dval' = [ dval EXCEPT ![i] = v0 ]
        /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
        /\ UNCHANGED << v, w, nCrash, sntMsgs, rcvdMsgs, V >>
     \/ /\ \A j \in 1..N : \E m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.sndr = j
        /\ \A v0 \in Values :
           Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.wValue = v0 }) < N - T
        /\ pc' = [ pc EXCEPT ![i] = "CHOOSE" ]
        /\ UNCHANGED << v, w, dval, nCrash, sntMsgs, rcvdMsgs, V >>

Choose(i) ==
  /\ pc[i] = "CHOOSE"
  /\ dval' = [ dval EXCEPT ![i] =
                (CHOOSE tV \in Values : \E j \in 1..N : tV = V[i][j]) ]
  /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
  /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>

Next == \E i \in 1..N :
  \/ Crash(i) \/ Receive(i) \/ BcastPhs1(i) \/ Phs1(i)
  \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i)
  \/ (\A p \in 1..N : pc[p] \in {"CRASH", "DONE"} /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars
       /\ WF_vars(\E i \in 1..N: Receive(i) \/ BcastPhs1(i) \/ Phs1(i)
                                 \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i))

TypeOK ==
  /\ V \in [ 1..N -> [ 1..N -> { Bottom } \cup Values ] ]
  /\ v \in [ 1..N -> Values ]
  /\ pc \in [ 1..N -> {"BCAST1","PHS1","PREP","BCAST2","PHS2","DONE","CRASH","CHOOSE"} ]
  /\ w \in [ 1..N -> { Bottom } \cup Values ]
  /\ dval \in [ 1..N -> { Bottom } \cup Values ]
  /\ nCrash \in 0..F
  /\ sntMsgs \in SUBSET Msgs
  /\ rcvdMsgs \in [ 1..N -> SUBSET Msgs ]

Validity == \A i \in 1..N : dval[i] # Bottom => \E j \in 1..N : dval[i] = v[j]
Agreement == \A i, j \in 1..N : (dval[i] # Bottom \/ dval[j] # Bottom) => dval[i] = dval[j]
Termination == <>(\A i \in 1..N : pc[i] \in {"CRASH", "DONE"})
Condition1 == Cardinality({ j \in 1..N : v[j] = MAX(v) }) > F
RealTermination == Condition1 => Termination
====