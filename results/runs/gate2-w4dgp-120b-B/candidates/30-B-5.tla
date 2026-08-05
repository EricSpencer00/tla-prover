---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS N, F, T, Values, Bottom

ASSUME 2 * T < N /\ 0 <= F /\ F <= T /\ 0 < N

VARIABLES pc, v, w, dval, nCrash, sntMsgs, rcvdMsgs

vars == << pc, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>


Status == { "BCAST1", "PHS1", "PREP","BCAST2", "PHS2", "DONE", "CRASH", "CHOOSE" }

Msg1s == [ type : {"Phs1"}, value : Values, sndr : 1..N ]
Msg2s == [ type : {"Phs2"}, value : Values, wValue : Values, sndr : 1..N ]
Msgs == Msg1s \cup Msg2s

MAX(arr) == CHOOSE maxVal \in Values :
              /\ \E p \in 1..N : arr[p] = maxVal
              /\ \A p \in 1..N : maxVal >= arr[p]

Init ==
  /\ pc = [ i \in 1..N |-> "BCAST1" ]
  /\ v \in [ 1..N -> Values ]
  /\ w = [ i \in 1..N |-> Bottom ]
  /\ dval = [ i \in 1..N |-> Bottom ]
  /\ nCrash = 0
  /\ sntMsgs = {}
  /\ rcvdMsgs = [ i \in 1..N |-> {} ]

\* If there are less than F faulty processes, process i becomes faulty.
Crash(i) ==
  /\ nCrash < F
  /\ pc[i] # "CRASH"
  /\ nCrash' = nCrash + 1
  /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
  /\ UNCHANGED << v, w, dval, sntMsgs, rcvdMsgs >>

\* A broadcasted message is received and recorded into V.
\* The message type must match the phase; otherwise it is not yet usable and
\* stays pending for a later Receive attempt (never consumed here).
Receive(i) ==
  \E msg \in sntMsgs :
    /\ pc[i] # "CRASH"
    /\ pc[i] = (IF msg.type = "Phs1" THEN "PHS1" ELSE "PHS2")
    /\ msg \notin rcvdMsgs[i]
    /\ rcvdMsgs' = [ rcvdMsgs EXCEPT ![i] = rcvdMsgs[i] \cup { msg } ]
    /\ V' = [ V EXCEPT ![i][msg.sndr] = msg.value ]
    /\ UNCHANGED << pc, v, w, dval, nCrash, sntMsgs >>

\* Broadcasts PHASE1(v_i, i).
BcastPhs1(i) ==
  /\ pc[i] = "BCAST1"
  /\ pc' = [ pc EXCEPT ![i] = "PHS1" ]
  /\ sntMsgs' = sntMsgs \cup { [ type |-> "Phs1", value |-> v[i], sndr |-> i ] }
  /\ UNCHANGED << v, w, dval, nCrash, rcvdMsgs >>

\* With at least N - T PHASE1 messages from distinct processes, a process updates
\* its view and makes an estimation.
Phs1(i) ==
  /\ pc[i] = "PHS1"
  /\ Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs1" }) >= N - T
  /\ pc' = [ pc EXCEPT ![i] = "BCAST2" ]
  /\ w' = [ w EXCEPT ![i] = MAX(V[i]) ]
  /\ UNCHANGED << v, dval, nCrash, sntMsgs, rcvdMsgs >>

\* Broadcasts PHASE2(w_i, i).
BcastPhs2(i) ==
  /\ pc[i] = "BCAST2"
  /\ pc' = [ pc EXCEPT ![i] = "PHS2" ]
  /\ sntMsgs' = sntMsgs \cup {
        [ type |-> "Phs2", value |-> v[i], wValue |-> w[i], sndr |-> i ]
      }
  /\ UNCHANGED << v, w, dval, nCrash, rcvdMsgs >>

\* A process decides by quorum on a value v0 in its PHASE2 messages, or, if
\* no value has a quorum among all N PHASE2 messages (the fallback), deterministically
\* CHOOSE a value from its view -- the guarded disjunction makes this exclusive with
\* the quorum rule.
Phs2(i) ==
  /\ pc[i] = "PHS2"
  /\ \/ \E v0 \in Values : /\ Cardinality({
                        m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.wValue = v0
                      }) >= N - T
                    /\ dval' = [ dval EXCEPT ![i] = v0 ]
                    /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
                    /\ UNCHANGED << v, w, nCrash, sntMsgs, rcvdMsgs >>
     \/ /\ \A m \in rcvdMsgs[i] : m.type = "Phs2"
        /\ \A v0 \in Values :
              Cardinality({ m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.wValue = v0 })
                < N - T
        /\ pc' = [ pc EXCEPT ![i] = "CHOOSE" ]
        /\ UNCHANGED << v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

\* When all PHASE2 messages have been received, the process deterministically
\* chooses a value appearing in its view.
Choose(i) ==
  /\ pc[i] = "CHOOSE"
  /\ dval' = [ dval EXCEPT ![i] = (CHOOSE t \in Values : \E j \in 1..N : t = V[i][j]) ]
  /\ pc' = [ pc EXCEPT ![i] = "DONE" ]
  /\ UNCHANGED << v, w, nCrash, sntMsgs, rcvdMsgs >>

Next == \E i \in 1..N : Crash(i) \/ Receive(i) \/ BcastPhs1(i)
                               \/ Phs1(i) \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i)

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N :
        Crash(i) \/ Receive(i) \/ BcastPhs1(i) \/ Phs1(i)
        \/ BcastPhs2(i) \/ Phs2(i) \/ Choose(i))

TypeOK ==
  /\ pc \in [ 1..N -> Status ]
  /\ v \in [ 1..N -> Values ]
  /\ w \in [ 1..N -> { Bottom } \cup Values ]
  /\ dval \in [ 1..N -> { Bottom } \cup Values ]
  /\ nCrash \in 0..F
  /\ sntMsgs \subseteq Msgs
  /\ rcvdMsgs \in [ 1..N -> SUBSET Msgs ]

\* If a process decides v, then v was proposed by some process.
Validity == \A i \in 1..N : dval[i] # Bottom => \E j \in 1..N : dval[i] = v[j]

\* No two processes decide differently.
Agreement == \A i, j \in 1..N : (dval[i] # Bottom \/ dval[j] # Bottom) => dval[i] = dval[j]

\* Every correct process eventually decides.
Termination == <>(\A i \in 1..N : pc[i] = "CRASH" \/ pc[i] = "DONE")

\* At least F + 1 processes start with the greatest value.
Condition1 == Cardinality({ j \in 1..N : v[j] = MAX(v) }) > F

\* If the input satisfies Condition1, the algorithm terminates.
RealTermination == Condition1 => Termination

====