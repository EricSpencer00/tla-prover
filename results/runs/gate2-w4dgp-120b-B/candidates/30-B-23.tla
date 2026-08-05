---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets, TLC

CONSTANT N, F, T, Values, Bottom

ASSUME 2 * T < N /\ 0 <= F /\ F <= T
ASSUME \A v \in Values: v # Bottom

VARIABLES pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs

vars == << pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

Proc == 1..N
Status == { "BCAST1", "PHS1", "PREP", "BCAST2", "PHS2", "DONE", "CRASH", "CHOOSE" }

Msgs == [ type : {"Phs1","Phs2"} , value : Values ,
          wValue : Values \cup {Bottom}, sndr : Proc ]

MAX(arr) == CHOOSE maxV \in Values : /\ (\E p \in Proc: arr[p] = maxV)
                                    /\ (\A p \in Proc: maxV >= arr[p])

Init ==
  /\ V = [ i \in Proc |-> [ j \in Proc |-> Bottom ] ]
  /\ v \in [ Proc -> Values ]
  /\ pc = [ i \in Proc |-> "BCAST1" ]
  /\ w = [ i \in Proc |-> Bottom ]
  /\ dval = [ i \in Proc |-> Bottom ]
  /\ nCrash = 0
  /\ sntMsgs = {}
  /\ rcvdMsgs = [ i \in Proc |-> {} ]

Phs1Msg(vp,i)  == [ type |-> "Phs1", value |-> vp, sndr |-> i ]
Phs2Msg(vp,wp,i) == [ type |-> "Phs2", value |-> vp, wValue |-> wp, sndr |-> i ]

Crash(i) ==
  /\ nCrash < F
  /\ pc[i] # "CRASH"
  /\ nCrash' = nCrash + 1
  /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
  /\ UNCHANGED << V, v, w, dval, sntMsgs, rcvdMsgs >>

\* A message is only received if its type/phase matches the recipient's current
\* phase -- otherwise the delivery is disallowed and the message stays pending
\* for that process's own later Receive attempt (once its phase catches up).
Receive(i) ==
  \E msg \in Msgs :
    /\ pc[i] # "CRASH"
    /\ pc[i] = "PHS1" => msg.type = "Phs1"
    /\ pc[i] = "PHS2" => msg.type = "Phs2"
    /\ msg \in sntMsgs
    /\ msg \notin rcvdMsgs[i]
    /\ rcvdMsgs' = [ rcvdMsgs EXCEPT ![i] = rcvdMsgs[i] \cup { msg } ]
    /\ LET j == msg.sndr IN V' = [ V EXCEPT ![i][j] = msg.value ]
    /\ UNCHANGED << pc, v, w, dval, nCrash, sntMsgs >>

BcastPhs1(i) ==
  /\ pc[i] = "BCAST1"
  /\ pc' = [ pc EXCEPT ![i] = "PHS1" ]
  /\ sntMsgs' = sntMsgs \cup { Phs1Msg(v[i],i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

Phs1(i) ==
  /\ pc[i] = "PHS1"
  /\ Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs1"}) >= N - T
  /\ pc' = [ pc EXCEPT ![i] = "BCAST2" ]
  /\ w' = [ w EXCEPT ![i] = MAX(V[i]) ]
  /\ UNCHANGED << V, v, dval, nCrash, sntMsgs, rcvdMsgs >>

BcastPhs2(i) ==
  /\ pc[i] = "BCAST2"
  /\ pc' = [ pc EXCEPT ![i] = "PHS2" ]
  /\ sntMsgs' = sntMsgs \cup { Phs2Msg(v[i], w[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

\* The majority-decision check has strict priority and is the only guarded
\* exit from PHASE2; only when no value has a deciding quorum among the full
\* set of N PHASE2 echoes does the deterministic fallback return(F(Y_i))
\* fire -- which is then mutually exclusive with the quorum rule.
Phs2(i) ==
  \/ /\ pc[i] = "PHS2"
     /\ \E v0 \in Values :
          /\ Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.wValue = v0 }) >= N - T
          /\ dval' = [ dval EXCEPT ![i] = v0 ]
          /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
          /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>
     \/ /\ pc[i] = "PHS2"
        /\ \A m \in rcvdMsgs[i]: m.type = "Phs2"
        /\ \A v0 \in Values:
             Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.wValue = v0 }) < N - T
        /\ pc' = [ pc EXCEPT ![i] = "CHOOSE" ]
        /\ UNCHANGED << V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

Choose(i) ==
  /\ pc[i] = "CHOOSE"
  /\ dval' = [ dval EXCEPT ![i] = (CHOOSE tV \in Values: \E j \in Proc: tV = V[i][j]) ]
  /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
  /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>

Next == \E i \in Proc :
  \/ Crash(i) \/ Receive(i) \/ BcastPhs1(i) \/ Phs1(i)
  \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i)
  \/ /\ \A p \in Proc : pc[p] \in {"CRASH","DONE"}
     /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
       /\ WF_vars(\E i \in Proc: Crash(i) \/ Receive(i) \/ BcastPhs1(i)
                                   \/ Phs1(i) \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i))

TypeOK ==
  /\ V \in [ Proc -> [ Proc -> {Bottom} \cup Values ] ]
  /\ v \in [ Proc -> Values ] /\ w \in [ Proc -> {Bottom} \cup Values ]
  /\ dval \in [ Proc -> {Bottom} \cup Values ] /\ pc \in [ Proc -> Status ]
  /\ nCrash \in 0..F /\ sntMsgs \subseteq Msgs
  /\ rcvdMsgs \in [ Proc -> SUBSET Msgs ]

Validity == \A i \in Proc: dval[i] # Bottom => \E j \in Proc: dval[i] = v[j]
Agreement == \A i, j \in Proc : (dval[i] # Bottom \/ dval[j] # Bottom) => dval[i] = dval[j]
Termination == <> (\A i \in Proc: pc[i] \in {"CRASH","DONE"})
Condition1 == Cardinality({ j \in Proc: v[j] = MAX(v) }) > F
RealTermination == Condition1 => Termination
====