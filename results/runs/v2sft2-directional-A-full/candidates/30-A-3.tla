---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F, Values, Bottom

\* --------------------------------------------------------------------
\* Derived constants
\* --------------------------------------------------------------------
TypeOK ==
  /\ N \in Nat
  /\ 0 \le T
  /\ 0 \le F
  /\ F <= T
  /\ 2*T < N
  /\ Values \subseteq Nat
  /\ Bottom \in Nat
  /\ Bottom \notin Values
  /\ Values \cup {Bottom} \subseteq Nat

ValuesSet == Values

\* --------------------------------------------------------------------
\* Types
\* --------------------------------------------------------------------
ProcSet == 1 .. N
Val == ValuesSet \cup {Bottom}
MsgType == {"Phase1", "Phase2"}
EstVal == ValuesSet \cup {Bottom}

\* --------------------------------------------------------------------
\* Message definition
\* --------------------------------------------------------------------
\* Phase1 messages carry only a value
Phase1Msg == [type : MsgType, val : Val, sndr : ProcSet]
Phase2Msg == [type : MsgType, val : Val, est : EstVal, sndr : ProcSet]

Msg == Phase1Msg \/ Phase2Msg

\* --------------------------------------------------------------------
\* State variables
\* --------------------------------------------------------------------
VARIABLES
  loc,          \* control location of each process
  val,          \* proposed value of each process
  est,          \* estimated value computed after phase1
  dec,          \* decision value (Bottom means undecided)
  view,         \* N-by-N matrix of known values from each sender
  cr,           \* number of crashed processes
  sent,         \* set of messages already broadcast
  recv          \* mapping from each process to the set of messages it has received

\* --------------------------------------------------------------------
\* Control locations
\* --------------------------------------------------------------------
LocSet == {"BroadcastP1", "WaitP1", "BroadcastP2", "WaitP2",
           "Choosing", "Done", "Crashed"}

\* --------------------------------------------------------------------
\* Initial state
\* --------------------------------------------------------------------
Init ==
  /\ cr = 0
  /\ sent = {}
  /\ \E i \in ProcSet :
        /\ loc[i] = "BroadcastP1"
        /\ val[i] \in ValuesSet
        /\ est[i] = Bottom
        /\ dec[i] = Bottom
        /\ view[i] = [j \in ProcSet |-> Bottom]
  /\ \A i \in ProcSet : recv[i] = {}

\* --------------------------------------------------------------------
\* Helper predicates
\* --------------------------------------------------------------------
Send[pid, m] ==
  /\ m \in Msg
  /\ m.sndr = pid
  /\ sent' = sent \cup {m}
  /\ UNCHANGED <<loc, val, est, dec, view, cr, recv>>

Recv[pid, m] ==
  /\ m \in sent
  /\ m.type = "Phase1"
  /\ view[pid][m.sndr] = m.val
  /\ recv[pid] = recv[pid] \cup {m}
  /\ UNCHANGED <<loc, val, est, dec, cr, sent>>

RecvPhase2[pid, m] ==
  /\ m \in sent
  /\ m.type = "Phase2"
  /\ view[pid][m.sndr] = m.val
  /\ recv[pid] = recv[pid] \cup {m}
  /\ UNCHANGED <<loc, val, est, dec, cr, sent>>

\* --------------------------------------------------------------------
\* Transition actions
\* --------------------------------------------------------------------
BroadcastP1(pid) ==
  /\ loc[pid] = "BroadcastP1"
  /\ Send(pid, [type |-> "Phase1", val |-> val[pid], sndr |-> pid])

WaitP1(pid) ==
  /\ loc[pid] = "WaitP1"
  /\ \E m \in sent :
        /\ m.type = "Phase1"
        /\ m.sndr \in ProcSet
        /\ Recv(pid, m)

ComputeEst(pid) ==
  /\ loc[pid] = "WaitP1"
  /\ \E msgs \subseteq { m \in sent : m.type = "Phase1" /\ m.sndr \in ProcSet } :
        /\ Cardinality(msgs) >= N - T
        /\ est' = [est EXCEPT ![pid] = Max({ view[pid][j] : j \in { m.sndr : m \in msgs } })]
        /\ loc' = [loc EXCEPT ![pid] = "BroadcastP2"]
        /\ UNCHANGED <<val, dec, view, cr, sent, recv>>

BroadcastP2(pid) ==
  /\ loc[pid] = "BroadcastP2"
  /\ Send(pid, [type |-> "Phase2", val |-> val[pid], est |-> est[pid], sndr |-> pid])

WaitP2(pid) ==
  /\ loc[pid] = "WaitP2"
  /\ \E m \in sent :
        /\ m.type = "Phase2"
        /\ RecvPhase2(pid, m)

DecideEst(pid) ==
  /\ loc[pid] = "WaitP2"
  /\ \E msgs \subseteq { m \in sent : m.type = "Phase2" /\ m.sndr \in ProcSet } :
        /\ Cardinality(msgs) >= N - T
        /\ \E e \in EstVal :
               /\ \A m \in msgs : m.est = e
               /\ dec' = [dec EXCEPT ![pid] = e]
               /\ loc' = [loc EXCEPT ![pid] = "Done"]
               /\ UNCHANGED <<val, est, view, cr, sent, recv>>

NoDecide(pid) ==
  /\ loc[pid] = "WaitP2"
  /\ \E msgs \subseteq { m \in sent : m.type = "Phase2" /\ m.sndr \in ProcSet } :
        /\ Cardinality(msgs) = N
        /\ loc' = [loc EXCEPT ![pid] = "Choosing"]
        /\ UNCHANGED <<val, est, dec, view, cr, sent, recv>>

Choosing(pid) ==
  /\ loc[pid] = "Choosing"
  /\ dec' = [dec EXCEPT ![pid] = OneVal(view[pid])]
  /\ loc' = [loc EXCEPT ![pid] = "Done"]
  /\ UNCHANGED <<val, est, view, cr, sent, recv>>

OneVal(v) ==
  LET vals == { v[j] : j \in ProcSet } IN
  IF vals \ {Bottom} = {} THEN Bottom
  ELSE CHOOSE x \in vals : x \in ValuesSet

Crash(pid) ==
  /\ cr < F
  /\ cr' = cr + 1
  /\ loc' = [loc EXCEPT ![pid] = "Crashed"]
  /\ UNCHANGED <<val, est, dec, view, sent, recv>>

Next ==
  \/ \E pid \in ProcSet : BroadcastP1(pid)
  \/ \E pid \in ProcSet : WaitP1(pid)
  \/ \E pid \in ProcSet : ComputeEst(pid)
  \/ \E pid \in ProcSet : BroadcastP2(pid)
  \/ \E pid \in ProcSet : WaitP2(pid)
  \/ \E pid \in ProcSet : DecideEst(pid)
  \/ \E pid \in ProcSet : NoDecide(pid)
  \/ \E pid \in ProcSet : Choosing(pid)
  \/ \E pid \in ProcSet : Crash(pid)

\* --------------------------------------------------------------------
\* Specification
\* --------------------------------------------------------------------
Spec == Init /\ [][Next]_<<loc, val, est, dec, view, cr, sent, recv>>

\* --------------------------------------------------------------------
\* Safety invariants
\* --------------------------------------------------------------------
TypeOK ==
  /\ \A i \in ProcSet :
        /\ loc[i] \in LocSet
        /\ val[i] \in Val
        /\ est[i] \in EstVal
        /\ dec[i] \in EstVal
        /\ view[i] \in [ProcSet -> Val]
  /\ cr \in 0..F
  /\ sent \subseteq Msg
  /\ \A i \in ProcSet : recv[i] \subseteq sent

Validity ==
  /\ \A i \in ProcSet :
        /\ dec[i] = Bottom
        \/ dec[i] \in ValuesSet
        /\ \E j \in ProcSet : dec[i] = val[j]

Agreement ==
  \A i, j \in ProcSet :
        /\ dec[i] \neq Bottom
        /\ dec[j] \neq Bottom
        => dec[i] = dec[j]

\* --------------------------------------------------------------------
\* Properties for TLC
\* --------------------------------------------------------------------
\* (none needed; properties are defined as invariants above)

====