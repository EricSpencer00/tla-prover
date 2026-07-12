---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
ProcSet == 1..N
ValSet == Values \ {Bottom}
MaxVal == MAX(ValSet)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Loc == {"BroadcastPhase1", "WaitPhase1", "Prepare", "BroadcastPhase2",
        "WaitPhase2", "Done", "Crashed", "Choosing"}

MsgType == {"Phase1", "Phase2"}
MsgVType == {"Phase1", "Phase2"}

Msg == [type: MsgType, sender: ProcSet, val: Values, est: Values?]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES loc,             \* process locations
          val,             \* proposed values
          est,             \* estimated values
          dec,             \* decision values
          crashed,         \* set of crashed processes
          sent,            \* set of messages that have been sent
          recv              \* mapping from process to set of received messages

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
BottomVal == Bottom

\* Initialise local view: all entries Bottom
initLocalView == [p \in ProcSet |-> [q \in ProcSet |-> BottomVal]]

\* Count of crashed processes
crashedCount == Cardinality(crashed)

\* Helper: whether a process has received at least N-T distinct phase-1 messages
EnoughPhase1Msgs(p) ==
    Cardinality({ m \in recv[p] : m.type = "Phase1" }) >= (N - T)

\* Helper: whether a process has received at least N-T distinct phase-2 messages with the same estimated value
EnoughPhase2Msgs(p) ==
    EXISTS estVal \in ValSet :
      Cardinality({ m \in recv[p] : m.type = "Phase2" /\ m.est = estVal }) >= (N - T)

\* Helper: the set of estimated values received by a process
EstSet(p) == { m.est : m \in recv[p] : m.type = "Phase2" }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ loc = [p \in ProcSet |-> "BroadcastPhase1"]
    /\ val = [p \in ProcSet |-> [x \in ValSet |-> Propose(p)]]
    /\ est = [p \in ProcSet |-> Bottom]
    /\ dec = [p \in ProcSet |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [p \in ProcSet |-> {}]
    /\ \A p \in ProcSet : val[p] \in ValSet

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
    /\ loc[p] = "BroadcastPhase1"
    /\ \E m \in { [type |-> "Phase1", sender |-> p, val |-> val[p], est |-> Bottom] } :
          /\ m \notin sent
          /\ sent' = sent \cup {m}
    /\ loc' = [loc EXCEPT ![p] = "WaitPhase1"]
    /\ UNCHANGED <<val, est, dec, crashed, recv>>

ReceivePhase1(p, m) ==
    /\ loc[p] \in {"WaitPhase1", "Prepare"}
    /\ m \in sent
    /\ m.type = "Phase1"
    /\ p \notin crashed
    /\ recv' = [recv EXCEPT ![p] = @ \cup {m}]
    /\ est' = [est EXCEPT ![p] = MAX({ est[p], m.val })]
    /\ UNCHANGED <<loc, val, dec, crashed, sent>>

ComputeEstimate(p) ==
    /\ loc[p] = "WaitPhase1"
    /\ EnoughPhase1Msgs(p)
    /\ est' = [est EXCEPT ![p] = MAX({ est[p] } \cup { m.val : m \in recv[p], m.type = "Phase1" })]
    /\ loc' = [loc EXCEPT ![p] = "BroadcastPhase2"]
    /\ UNCHANGED <<val, dec, crashed, sent, recv>>

BroadcastPhase2(p) ==
    /\ loc[p] = "BroadcastPhase2"
    /\ \E m \in { [type |-> "Phase2", sender |-> p, val |-> val[p], est |-> est[p]] } :
          /\ m \notin sent
          /\ sent' = sent \cup {m}
    /\ loc' = [loc EXCEPT ![p] = "WaitPhase2"]
    /\ UNCHANGED <<val, est, dec, crashed, recv>>

ReceivePhase2(p, m) ==
    /\ loc[p] \in {"WaitPhase2", "Choosing"}
    /\ m \in sent
    /\ m.type = "Phase2"
    /\ p \notin crashed
    /\ recv' = [recv EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED <<loc, val, est, dec, crashed, sent>>

DecidePhase2(p, estVal) ==
    /\ loc[p] = "WaitPhase2"
    /\ EXISTS estVal \in ValSet :
          Cardinality({ m \in recv[p] : m.type = "Phase2" /\ m.est = estVal }) >= (N - T)
          /\ estVal = MAX({ m.est : m \in recv[p], m.type = "Phase2" })
    /\ dec' = [dec EXCEPT ![p] = estVal]
    /\ loc' = [loc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<val, est, crashed, sent, recv>>

ChoosingState(p) ==
    /\ loc[p] = "WaitPhase2"
    /\ ~EnoughPhase2Msgs(p)
    /\ loc' = [loc EXCEPT ![p] = "Choosing"]
    /\ UNCHANGED <<val, est, dec, crashed, sent, recv>>

Choose(p) ==
    /\ loc[p] = "Choosing"
    /\ \E v \in { m.val : m \in recv[p], m.type = "Phase1" } :
          v \in ValSet
    /\ dec' = [dec EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<val, est, crashed, sent, recv>>

Crash(p) ==
    /\ p \notin crashed
    /\ crashedCount < F
    /\ crashed' = crashed \cup {p}
    /\ loc' = [loc EXCEPT ![p] = "Crashed"]
    /\ UNCHANGED <<val, est, dec, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in ProcSet : BroadcastPhase1(p)
    \/ \E p \in ProcSet, m \in sent : ReceivePhase1(p, m)
    \/ \E p \in ProcSet : ComputeEstimate(p)
    \/ \E p \in ProcSet : BroadcastPhase2(p)
    \/ \E p \in ProcSet, m \in sent : ReceivePhase2(p, m)
    \/ \E p \in ProcSet, estVal \in ValSet : DecidePhase2(p, estVal)
    \/ \E p \in ProcSet : ChoosingState(p)
    \/ \E p \in ProcSet : Choose(p)
    \/ \E p \in ProcSet : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<loc, val, est, dec, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (optional)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ loc \in [ProcSet -> Loc]
    /\ val \in [ProcSet -> [ProcSet -> Values]]
    /\ est \in [ProcSet -> Values]
    /\ dec \in [ProcSet -> Values]
    /\ crashed \subseteq ProcSet
    /\ sent \subseteq Msg
    /\ recv \in [ProcSet -> SUBSET Msg]
    /\ \A p \in ProcSet : (loc[p] = "Crashed") => dec[p] = Bottom

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
Validity ==
    \A p \in ProcSet :
        (dec[p] \in ValSet) => (EXISTS q \in ProcSet : val[q][p] = dec[p])

Agreement ==
    \A p, q \in ProcSet :
        (dec[p] \in ValSet /\ dec[q] \in ValSet) => dec[p] = dec[q]

====