---- MODULE cbc_max ====
(* A conditional-consensus protocol based on the maximal proposal value (C1 in
   [1]). It originally had two TLC-detectable defects in the Receive action:
   (1) an UNCHANGED on V on the same line that LET-bound V' was assigned, which
       silently forced V' = V and dropped the broadcast's effect; (2) an else-branch
       that marked a message received even when it could not yet be used, so it
       got dropped forever and the decision step could later CHOOSE from a row
       still carrying Bottom instead of a true witness. Both are fixed below. *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS N, F, T, Values, Bottom

ASSUME 2 * T < N /\ 0 <= F /\ F <= T /\ 0 < N /\ \A v \in Values: v # Bottom

VARIABLES pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs
vars == << pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

Msg1s == [ type : {"Phs1"}, value : Values, sndr : 1..N ]
Msg2s == [ type : {"Phs2"}, value : Values, wValue : Values, sndr : 1..N ]
Msgs  == Msg1s \cup Msg2s
Status == { "BCAST1", "PHS1", "PREP", "BCAST2", "PHS2", "DONE", "CRASH", "CHOOSE" }

Phs1Msg(v,i) == [ type |-> "Phs1", value |-> v, sndr |-> i ]
Phs2Msg(v,w,i) == [ type |-> "Phs2", value |-> v, wValue |-> w, sndr |-> i ]

MAX(a) == CHOOSE m \in Values :
            /\ (\E i \in 1..N : a[i] = m) /\ (\A i \in 1..N : m >= a[i])

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
  /\ pc[i] # "CRASH" /\ nCrash < F
  /\ nCrash' = nCrash + 1
  /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
  /\ UNCHANGED << V, v, w, dval, sntMsgs, rcvdMsgs >>

(* Receive a pending message, but only one whose phase now matches this
   process's state -- otherwise it stays pending for a later attempt. *)
Receive(i) ==
  LET match == \/ pc[i] = "PHS1" /\ msg.type = "Phs1" \/ pc[i] = "PHS2" /\ msg.type = "Phs2" IN
  \E msg \in Msgs :
    /\ pc[i] # "CRASH" /\ match
    /\ msg \in sntMsgs /\ msg \notin rcvdMsgs[i]
    /\ rcvdMsgs' = [ rcvdMsgs EXCEPT ![i] = rcvdMsgs[i] \cup { msg } ]
    /\ V' = [ V EXCEPT ![i][msg.sndr] = msg.value ]
    /\ UNCHANGED << pc, v, w, dval, nCrash, sntMsgs >>

BcastPhs1(i) ==
  /\ pc[i] = "BCAST1"
  /\ pc' = [ pc EXCEPT ![i] = "PHS1" ]
  /\ sntMsgs' = sntMsgs \cup { Phs1Msg(v[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

Phs1(i) ==
  /\ pc[i] = "PHS1"
  /\ Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs1" }) >= N - T
  /\ pc'  = [ pc EXCEPT ![i] = "BCAST2" ]
  /\ w'   = [ w EXCEPT ![i] = MAX(V[i]) ]
  /\ UNCHANGED << V, v, dval, nCrash, sntMsgs, rcvdMsgs >>

BcastPhs2(i) ==
  /\ pc[i] = "BCAST2"
  /\ pc' = [ pc EXCEPT ![i] = "PHS2" ]
  /\ sntMsgs' = sntMsgs \cup { Phs2Msg(v[i], w[i], i) }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

(* A process decides on a quorum value when it exists; otherwise, with no
   quorum possible among all PHASE2 messages, it CHOOSES from its own view. *)
Phs2(i) ==
  \/ /\ Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.wValue = v0 })
        >= N - T
     /\ dval' = [ dval EXCEPT ![i] = v0 ]
     /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
     /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>
  \/ /\ (\A j \in 1..N: \E m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.sndr = j)
     /\ \A v0 \in Values :
          Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.wValue = v0 }) < N - T
     /\ pc' = [ pc EXCEPT ![i] = "CHOOSE" ]
     /\ UNCHANGED << V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

Choose(i) ==
  /\ pc[i] = "CHOOSE"
  /\ dval' = [ dval EXCEPT ![i] = CHOOSE t \in Values : \E j \in 1..N : t = V[i][j] ]
  /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
  /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>

Next == \E i \in 1..N:
  Crash(i) \/ Receive(i) \/ BcastPhs1(i) \/ Phs1(i) \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i)
  \/ (\A p \in 1..N : pc[p] \in { "CRASH", "DONE" } /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars
       /\ WF_vars(\E i \in 1..N: Receive(i) \/ BcastPhs1(i) \/ Phs1(i)
                  \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i))

TypeOK ==
  /\ V \in [ 1..N -> [ 1..N -> { Bottom } \cup Values ] ]
  /\ v \in [ 1..N -> Values ]
  /\ pc \in [ 1..N -> Status ]
  /\ w \in [ 1..N -> { Bottom } \cup Values ]
  /\ dval \in [ 1..N -> { Bottom } \cup Values ]
  /\ nCrash \in 0..F
  /\ sntMsgs \in SUBSET Msgs
  /\ rcvdMsgs \in [ 1..N -> SUBSET Msgs ]

Validity == \A i \in 1..N : dval[i] # Bottom => (\E j \in 1..N : dval[i] = v[j])
Agreement == \A i, j \in 1..N : (dval[i] # Bottom \/ dval[j] # Bottom) => dval[i] = dval[j]
Termination == <>(\A i \in 1..N : pc[i] \in { "CRASH", "DONE" })
Condition1 == Cardinality({ j \in 1..N : v[j] = MAX(v) }) > F
RealTermination == Condition1 => Termination
====