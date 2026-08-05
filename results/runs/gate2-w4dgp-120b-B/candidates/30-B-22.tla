---- MODULE cbc_max ----
(* Conditional consensus with maximal value, from Mostefaoui et al., DSN 2003.
   PATCHED: two defects in Receive were traced by TLC to a canonical counterexample;
   both are fixed here with two minimal guarded-action changes. *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS N, T, Values, Bottom

ASSUME 2 * T < N /\ T >= 0 /\ 0 < N /\ \A v \in Values: v # Bottom

VARIABLES pc, V, v, w, dval, sntMsgs, rcvdMsgs

vars == << pc, V, v, w, dval, sntMsgs, rcvdMsgs >>
Proc == 1..N
Status == {"BCAST1","PHS1","BCAST2","PHS2","DONE","CHOOSE"}
Msg1s == [ type : {"Phs1"}, value : Values, sndr : Proc ]
Msg2s == [ type : {"Phs2"}, value : Values, wValue : Values, sndr : Proc ]
Msgs == Msg1s \cup Msg2s

MAX(arr) == CHOOSE m \in Values :
  /\ \E i \in Proc : arr[i] = m
  /\ \A i \in Proc : m >= arr[i]

Init ==
  /\ V = [ i \in Proc |-> [ j \in Proc |-> Bottom ] ]
  /\ v \in [ Proc -> Values ]
  /\ pc = [ i \in Proc |-> "BCAST1" ]
  /\ w = [ i \in Proc |-> Bottom ]
  /\ dval = [ i \in Proc |-> Bottom ]
  /\ sntMsgs = {}
  /\ rcvdMsgs = [ i \in Proc |-> {} ]

Crash(i) ==
  /\ pc[i] # "BCAST1"
  /\ pc' = [ pc EXCEPT ![i] = "BCAST1" ]
  /\ UNCHANGED << V, v, w, dval, sntMsgs, rcvdMsgs >>

(* Receive only messages the recipient is currently prepared to use; a not-yet-ready
   message is not consumed here (it stays pending for the process's own later attempt). *)
Receive(i) ==
  \E msg \in Msgs :
    /\ pc[i] # "BCAST1"
    /\ msg \in sntMsgs
    /\ msg \notin rcvdMsgs[i]
    /\ \/ /\ pc[i] = "PHS1" /\ msg.type = "Phs1"
          \/ /\ pc[i] = "PHS2" /\ msg.type = "Phs2"
    /\ rcvdMsgs' = [ rcvdMsgs EXCEPT ![i] = rcvdMsgs[i] \cup { msg } ]
    /\ V' = [ V EXCEPT ![i][msg.sndr] = msg.value ]
    /\ UNCHANGED << pc, v, w, dval, sntMsgs >>

BcastPhs1(i) ==
  /\ pc[i] = "BCAST1"
  /\ pc' = [ pc EXCEPT ![i] = "PHS1" ]
  /\ sntMsgs' = sntMsgs \cup { [ type |-> "Phs1", value |-> v[i], sndr |-> i ] }
  /\ UNCHANGED << V, v, w, dval, rcvdMsgs >>

Phs1(i) ==
  /\ pc[i] = "PHS1"
  /\ Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs1" }) >= N - T
  /\ pc' = [ pc EXCEPT ![i] = "BCAST2" ]
  /\ w' = [ w EXCEPT ![i] = MAX(V[i]) ]
  /\ UNCHANGED << V, v, dval, sntMsgs, rcvdMsgs >>

BcastPhs2(i) ==
  /\ pc[i] = "BCAST2"
  /\ pc' = [ pc EXCEPT ![i] = "PHS2" ]
  /\ sntMsgs' = sntMsgs \cup { [ type |-> "Phs2", value |-> v[i], wValue |-> w[i], sndr |-> i ] }
  /\ UNCHANGED << V, v, w, dval, rcvdMsgs >>

(* Decision is always guarded: the quorum rule takes strict priority over the
   fallback, exactly as in the source protocol's Fig. 3 (JACM 50(6)). *)
Phs2(i) ==
  /\ pc[i] = "PHS2"
  /\ \/ (\E v0 \in Values :
        /\ Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.wValue = v0 }) >= N - T
        /\ dval' = [ dval EXCEPT ![i] = v0 ]
        /\ pc' = [ pc EXCEPT ![i] = "DONE" ])
     \/ /\ \A v0 \in Values :
            Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.wValue = v0 }) < N - T
        /\ pc' = [ pc EXCEPT ![i] = "CHOOSE" ]
        /\ dval' = dval
  /\ UNCHANGED << V, v, w, sntMsgs, rcvdMsgs >>

Choose(i) ==
  /\ pc[i] = "CHOOSE"
  /\ dval' = [ dval EXCEPT ![i] = (CHOOSE t \in Values : \E j \in Proc : t = V[i][j]) ]
  /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
  /\ UNCHANGED << V, v, w, sntMsgs, rcvdMsgs >>

Next == \E i \in Proc :
  \/ Crash(i) \/ Receive(i) \/ BcastPhs1(i) \/ Phs1(i)
  \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E i \in Proc : Receive(i) \/ BcastPhs1(i) \/ Phs1(i) \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i))

TypeOK ==
  /\ V \in [ Proc -> [ Proc -> { Bottom } \cup Values ] ]
  /\ v \in [ Proc -> Values ]
  /\ pc \in [ Proc -> Status ]
  /\ w \in [ Proc -> { Bottom } \cup Values ]
  /\ dval \in [ Proc -> { Bottom } \cup Values ]
  /\ sntMsgs \in SUBSET Msgs
  /\ rcvdMsgs \in [ Proc -> SUBSET Msgs ]

Validity == \A i \in Proc : dval[i] # Bottom => \E j \in Proc : dval[i] = v[j]
Agreement == \A i, j \in Proc : (dval[i] # Bottom \/ dval[j] # Bottom) => dval[i] = dval[j]
Terminate == <>(\A i \in Proc : pc[i] = "DONE")
Condition1 == Cardinality({ j \in Proc : v[j] = MAX(v) }) > 0
RealTerm == Condition1 => Terminate

====