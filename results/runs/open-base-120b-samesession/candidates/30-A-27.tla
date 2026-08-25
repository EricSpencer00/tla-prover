---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    N,               \* number of processes
    T,               \* tolerance parameter
    F,               \* maximum number of actual crashes
    Values,          \* finite totally ordered set of proposal values
    Bottom           \* special bottom value not in Values

ASSUME 0 < N
ASSUME 2 * T < N
ASSUME 0 <= F /\ F <= T

\* ----------------------------------------------------------------------
\* Process identifiers
Proc == 1 .. N

\* ----------------------------------------------------------------------
\* Message definition
Message ==
    [type   : {"P1", "P2"},
     sender : Proc,
     value  : Values,
     est    : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    pc,             \* control location of each process
    view,           \* N-by-N matrix of known values (or Bottom)
    prop,           \* proposed value of each process
    est,            \* estimated value after phase 1
    dec,            \* decision value (Bottom if undecided)
    crashedCount,   \* number of crashed processes
    sent,           \* set of messages that have been broadcast
    recv            \* messages received by each process

vars == <<pc, view, prop, est, dec, crashedCount, sent, recv>>

\* ----------------------------------------------------------------------
\* Control locations
Locs == {"b1", "w1", "b2", "w2", "choosing", "done", "crashed"}

\* ----------------------------------------------------------------------
\* Helper definitions
Max(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE x \in S : \A y \in S : y <= x

CountSenders(p, mtype) ==
    { m.sender : m \in recv[p] /\ m.type = mtype }

CountEst(p, v) ==
    { m.sender : m \in recv[p] /\ m.type = "P2" /\ m.est = v }

AllSenders(p) ==
    { m.sender : m \in recv[p] }

\* ----------------------------------------------------------------------
\* Initialization
Init ==
    /\ pc = [p \in Proc |-> "b1"]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ prop \in [Proc -> Values]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions

BroadcastPhase1(p) ==
    /\ pc[p] = "b1"
    /\ sent' = sent \cup { [type |-> "P1",
                           sender |-> p,
                           value  |-> prop[p],
                           est    |-> Bottom] }
    /\ pc' = [pc EXCEPT ![p] = "w1"]
    /\ UNCHANGED <<view, prop, est, dec, crashedCount, recv>>

Receive(p, m) ==
    /\ m \in sent
    /\ m \notin recv[p]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ view' = 
        IF m.type = "P1" THEN
            [view EXCEPT ![p][m.sender] = m.value]
        ELSE
            [view EXCEPT ![p][m.sender] = m.est]
    /\ UNCHANGED <<pc, prop, est, dec, crashedCount, sent>>

ComputeEst(p) ==
    /\ pc[p] = "w1"
    /\ Cardinality(CountSenders(p, "P1")) >= N - T
    /\ est' = [est EXCEPT ![p] = Max({ view[p][q] : q \in Proc })]
    /\ pc' = [pc EXCEPT ![p] = "b2"]
    /\ UNCHANGED <<view, prop, dec, crashedCount, sent, recv>>

BroadcastPhase2(p) ==
    /\ pc[p] = "b2"
    /\ sent' = sent \cup { [type |-> "P2",
                           sender |-> p,
                           value  |-> prop[p],
                           est    |-> est[p]] }
    /\ pc' = [pc EXCEPT ![p] = "w2"]
    /\ UNCHANGED <<view, prop, est, dec, crashedCount, recv>>

Decide(p, v) ==
    /\ pc[p] = "w2"
    /\ v \in Values
    /\ Cardinality(CountEst(p, v)) >= N - T
    /\ dec' = [dec EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashedCount, sent, recv>>

MoveToChoosing(p) ==
    /\ pc[p] = "w2"
    /\ Cardinality(AllSenders(p)) = N
    /\ \A v \in Values : Cardinality(CountEst(p, v)) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, prop, est, dec, crashedCount, sent, recv>>

Choose(p) ==
    /\ pc[p] = "choosing"
    /\ LET candidates == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
       candidates # {}
    /\ let v == CHOOSE x \in candidates : TRUE in
       /\ dec' = [dec EXCEPT ![p] = v]
       /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashedCount, sent, recv>>

Crash(p) ==
    /\ pc[p] # "crashed"
    /\ crashedCount < F
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED <<view, prop, est, dec, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc, m \in sent : Receive(p, m)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : BroadcastPhase2(p)
    \/ \E p \in Proc, v \in Values : Decide(p, v)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ pc \in [Proc -> Locs]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ dec \in [Proc -> (Values \cup {Bottom})]
    /\ crashedCount \in Nat
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
Validity ==
    \A p \in Proc :
        dec[p] # Bottom =>
            \E q \in Proc : dec[p] = prop[q]

Agreement ==
    \A p, q \in Proc :
        /\ dec[p] # Bottom
        /\ dec[q] # Bottom
        => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* The required identifiers
SPECIFICATION Spec
INVARIANTS TypeOK, Validity, Agreement

====