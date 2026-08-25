---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    N,            \* number of processes
    T,            \* maximum tolerated faults
    F,            \* actual faults (upper bound)
    Values,       \* finite totally ordered set of proposal values
    Bottom        \* special bottom value (not in Values)

\* ----------------------------------------------------------------------
\* Process identifiers
Proc == 1..N

\* ----------------------------------------------------------------------
\* Control locations
PcValues == {"bcast1", "wait1", "bcast2", "wait2", "choosing", "done", "crashed"}

\* ----------------------------------------------------------------------
\* Message definition
Msg ==
    [type : {"phase1", "phase2"},
     sender : Proc,
     val : Values,
     est  : Values \cup {Bottom}]   \* for phase1 messages est = Bottom

\* ----------------------------------------------------------------------
\* Variables
VARIABLES
    pc,          \* [p \in Proc -> PcValues]
    view,        \* [p \in Proc -> [q \in Proc -> Values \cup {Bottom}]]
    prop,        \* [p \in Proc -> Values]                \* initial proposal
    est,         \* [p \in Proc -> Values \cup {Bottom}] \* estimated value after phase 1
    dec,         \* [p \in Proc -> Values \cup {Bottom}] \* decision value
    crashed,    \* SUBSET Proc                           \* set of crashed processes
    sent,        \* SUBSET Msg                            \* all messages that have been sent
    recv         \* [p \in Proc -> SUBSET Msg]            \* messages received by each process

\* ----------------------------------------------------------------------
\* Helper function: maximum of a non‑empty set of values (Values is totally ordered)
MaxVal(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE v \in S : \A w \in S : v >= w

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ pc = [p \in Proc |-> "bcast1"]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ prop \in [p \in Proc -> Values]            \* nondeterministic assignment
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Action: a non‑crashed process broadcasts a phase‑1 message
BroadcastPhase1(p) ==
    /\ p \in Proc \ setminus crashed
    /\ pc[p] = "bcast1"
    /\ let m == [type |-> "phase1", sender |-> p, val |-> prop[p], est |-> Bottom] in
       /\ sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<view, prop, est, dec, crashed, recv>>

\* ----------------------------------------------------------------------
\* Action: a process receives a phase‑1 message
ReceivePhase1(p, m) ==
    /\ p \in Proc \ setminus crashed
    /\ pc[p] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ m.sender \notin {msg.sender : msg \in recv[p]}
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ UNCHANGED <<pc, prop, est, dec, crashed, sent>>

\* ----------------------------------------------------------------------
\* Action: after having enough phase‑1 messages, compute estimate and move to phase‑2 broadcast
ComputeEst(p) ==
    /\ p \in Proc \ setminus crashed
    /\ pc[p] = "wait1"
    /\ LET senders == {msg.sender : msg \in recv[p] /\ msg.type = "phase1"} IN
       Cardinality(senders) >= N - T
    /\ LET vals == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
       est' = [est EXCEPT ![p] = MaxVal(vals)]
    /\ pc' = [pc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED <<view, prop, dec, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Action: broadcast a phase‑2 message
BroadcastPhase2(p) ==
    /\ p \in Proc \ setminus crashed
    /\ pc[p] = "bcast2"
    /\ let m == [type |-> "phase2", sender |-> p,
                val |-> prop[p], est |-> est[p]] in
       /\ sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<view, prop, est, dec, crashed, recv>>

\* ----------------------------------------------------------------------
\* Action: receive a phase‑2 message
ReceivePhase2(p, m) ==
    /\ p \in Proc \ setminus crashed
    /\ pc[p] = "wait2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ m.sender \notin {msg.sender : msg \in recv[p]}
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]   \* store the proposer’s value as before
    /\ UNCHANGED <<pc, prop, est, dec, crashed, sent>>

\* ----------------------------------------------------------------------
\* Action: decide when a value appears in at least N‑T phase‑2 messages
DecideByEstimate(p, v) ==
    /\ p \in Proc \ setminus crashed
    /\ pc[p] = "wait2"
    /\ v \in Values
    /\ LET msgs == {msg \in recv[p] : msg.type = "phase2" /\ msg.est = v} IN
       Cardinality({msg.sender : msg \in msgs}) >= N - T
    /\ dec' = [dec EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Action: move to choosing state after having heard from all N senders
MoveToChoosing(p) ==
    /\ p \in Proc \ setminus crashed
    /\ pc[p] = "wait2"
    /\ LET senders == {msg.sender : msg \in recv[p] /\ msg.type = "phase2"} IN
       senders = Proc
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, prop, est, dec, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Action: deterministic choice from local view and decide
ChooseAndDecide(p) ==
    /\ p \in Proc \ setminus crashed
    /\ pc[p] = "choosing"
    /\ LET vals == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
       vals # {}    \* there is at least one non‑bottom value
    /\ LET v == CHOOSE x \in vals : TRUE IN
       dec' = [dec EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Action: a process may crash (if fewer than F have crashed so far)
Crash(p) ==
    /\ p \in Proc \ setminus crashed
    /\ Cardinality(crashed) < F
    /\ crashed' = crashed \cup {p}
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<view, prop, est, dec, sent, recv>>

\* ----------------------------------------------------------------------
\* The Next-state relation is the disjunction of all possible actions
Next ==
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc, m \in Msg : ReceivePhase1(p, m)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : BroadcastPhase2(p)
    \/ \E p \in Proc, m \in Msg : ReceivePhase2(p, m)
    \/ \E p \in Proc, v \in Values : DecideByEstimate(p, v)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : ChooseAndDecide(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* State predicate for type correctness
TypeOK ==
    /\ pc \in [Proc -> PcValues]
    /\ view \in [Proc -> [Proc -> Values \cup {Bottom}]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> Values \cup {Bottom}]
    /\ dec \in [Proc -> Values \cup {Bottom}]
    /\ crashed \subseteq Proc
    /\ sent \subseteq Msg
    /\ recv \in [Proc -> SUBSET Msg]

\* ----------------------------------------------------------------------
\* Safety property: Validity
Validity ==
    \A p \in Proc :
        /\ dec[p] # Bottom
        => (\E q \in Proc : prop[q] = dec[p])

\* ----------------------------------------------------------------------
\* Safety property: Agreement
Agreement ==
    \A p, q \in Proc :
        /\ dec[p] # Bottom
        /\ dec[q] # Bottom
        => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* Specification
vars == <<pc, view, prop, est, dec, crashed, sent, recv>>

Spec ==
    Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants (named as required)
TypeOKInv == TypeOK
ValidityInv == Validity
AgreementInv == Agreement

\* ----------------------------------------------------------------------
\* THEOREMS (optional, can be used by the model checker)
THEOREM Spec => []TypeOKInv
THEOREM Spec => []ValidityInv
THEOREM Spec => []AgreementInv

====