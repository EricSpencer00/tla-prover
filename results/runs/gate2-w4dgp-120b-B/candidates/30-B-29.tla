---- MODULE cbc_max ----
(* A max-based conditional consensus protocol from Mostéfaoui et al., DSN 2003,
   where a process adopts the greatest value it has seen and decides when a
   quorum of phase-two echoes agrees. A message may arrive before its
   recipient is ready (phase or type mismatch), which is indistinguishable from a
   message that never existed, so the receiver must not both consume and discard
   such a message. The original (unpatched) version marked ANY pending message as
   received in the same step -- discarding its value -- and also listed V in
   UNCHANGED on the same line its assignment was made, so the assignment was
   silently dropped by the parser. Both defects are fixed here without
   changing the protocol's semantics. *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS N, F, T, Values, Bottom

ASSUME 2 * T < N /\ 0 <= F /\ F <= T /\ 0 < N
ASSUME \A v \in Values: v # Bottom

VARIABLES pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs

vars == << pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

Proc == 1..N
Status == { "BCAST1", "PHS1", "PREP","BCAST2", "PHS2", "DONE", "CRASH", "CHOOSE" }

Msgs == {[ type |-> "Phs1", value :> Values, sndr :> Proc ]
         \cup [ type |-> "Phs2", value :> Values, wValue :> Values, sndr :> Proc ]}

MAX(arr) ==
  CHOOSE m \in Values : /\ (\E i \in Proc: arr[i] = m) /\ (\A i \in Proc: m >= arr[i])

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
  /\ UNCHANGED << V, v, w, dval, sntMsgs, rcvdMsgs >>

(* A message is only consumable when it matches the receiver's current phase
   and type; a stale or mismatched message stays pending for a later attempt. *)
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
  /\ sntMsgs' = sntMsgs \cup { [ type |-> "Phs1", value |-> v[i], sndr |-> i ] }
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
  /\ sntMsgs' = sntMsgs \cup { [ type |-> "Phs2", value |-> v[i], wValue |-> w[i], sndr |-> i ] }
  /\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

(* PHASE2: a quorum can decide, or every message can be exhausted and the
   fallback CHOOSE is taken -- only when no quorum is available (the guard). *)
Phs2(i) ==
  /\ pc[i] = "PHS2"
  /\ \/ \E v0 \in Values:
        /\ Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.wValue = v0 }) >= N - T
        /\ dval' = [ dval EXCEPT ![i] = v0 ]
        /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
        /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>
     \/ /\ \A j \in Proc: \E m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.sndr = j
        /\ \A v0 \in Values:
             Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.wValue = v0 }) < N - T
        /\ pc' = [ pc EXCEPT ![i] = "CHOOSE" ]
        /\ UNCHANGED << V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

Choose(i) ==
  /\ pc[i] = "CHOOSE"
  /\ dval' = [ dval EXCEPT ![i] =
                (CHOOSE tV \in Values: (\E j \in Proc: tV = V[i][j])) ]
  /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
  /\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>

Next == \E i \in Proc:
  \/ Crash(i) \/ Receive(i) \/ BcastPhs1(i) \/ Phs1(i)
  \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i)
  \/ /\ \A p \in Proc: pc[p] \in {"CRASH","DONE"} /\ UNCHANGED vars

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(\E i \in Proc:
        Receive(i) \/ BcastPhs1(i) \/ Phs1(i) \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i))

TypeOK ==
  /\ V \in [ Proc -> [ Proc -> { Bottom } \cup Values ] ]
  /\ v \in [ Proc -> Values ] /\ pc \in [ Proc -> Status ]
  /\ w \in [ Proc -> { Bottom } \cup Values ]
  /\ dval \in [ Proc -> { Bottom } \cup Values ]
  /\ nCrash \in 0..F
  /\ sntMsgs \in SUBSET Msgs
  /\ rcvdMsgs \in [ Proc -> SUBSET Msgs ]

Validity == \A i \in Proc: dval[i] # Bottom => \E j \in Proc: dval[i] = v[j]
Agreement == \A i, j \in Proc: (dval[i] # Bottom \/ dval[j] # Bottom) => dval[i] = dval[j]

Termination == <>(\A i \in Proc: pc[i] \in {"CRASH","DONE"})
Condition1 == Cardinality({ i \in Proc: v[i] = MAX(v) }) > F
RealTermination == Condition1 => Termination

====