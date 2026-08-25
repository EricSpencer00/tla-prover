---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    N,            \* number of processes
    T,            \* tolerated faults
    F,            \* actual faults (bound)
    Values,       \* finite totally ordered set of proposal values
    Bottom        \* special bottom value, not in Values

ASSUME 0 < N
ASSUME 2 * T < N
ASSUME 0 <= F /\ F <= T

\* ======================================================================
\*   Process identifiers and auxiliary sets
\* ======================================================================
Proc == 1 .. N

LocSet == {"bcast1", "wait1", "bcast2", "wait2", "choosing", "done", "crashed"}

Message ==
    [type   : {"phase1", "phase2"},
     sender : Proc,
     value  : Values \cup {Bottom},
     est    : Values \cup {Bottom}]   \* est is used only for phase2 messages

\* ======================================================================
\*   State variables
\* ======================================================================
VARIABLES
    loc,        \* [p \in Proc -> LocSet]  current location of each process
    view,       \* [p \in Proc -> [q \in Proc -> Values \cup {Bottom}]]
    prop,       \* [p \in Proc -> Values]  the initial proposal of each process
    est,        \* [p \in Proc -> Values \cup {Bottom}]  estimated value after phase 1
    dec,        \* [p \in Proc -> Values \cup {Bottom}]  decision value (Bottom = undecided)
    msgs,       \* SUBSET Message   set of all messages that have been broadcast
    rcv,        \* [p \in Proc -> SUBSET Message]   messages received by each process
    crashCount  \* Nat               number of processes that have crashed

vars == << loc, view, prop, est, dec, msgs, rcv, crashCount >>

\* ======================================================================
\*   Helper definitions
\* ======================================================================
ReceivedPhase1(p) == { m \in rcv[p] : m.type = "phase1" }
ReceivedPhase2(p) == { m \in rcv[p] : m.type = "phase2" }

MaxInView(p) ==
    LET vals == { view[p][q] : q \in Proc } IN
    IF vals = {} THEN Bottom
    ELSE
        CHOOSE v \in vals :
            \A w \in vals : w <= v

\* ======================================================================
\*   Initial state
\* ======================================================================
Init ==
    /\ loc = [p \in Proc |-> "bcast1"]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ prop \in [p \in Proc -> Values]          \* nondeterministic proposals
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ msgs = {}
    /\ rcv = [p \in Proc |-> {}]
    /\ crashCount = 0

\* ======================================================================
\*   Phase‑1 actions
\* ======================================================================
BroadcastPhase1(p) ==
    /\ loc[p] = "bcast1"
    /\ LET m == [type |-> "phase1",
                sender |-> p,
                value  |-> prop[p],
                est    |-> Bottom] IN
       msgs' = msgs \cup {m}
    /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED << view, prop, est, dec, rcv, crashCount >>

ReceivePhase1(p, m) ==
    /\ m \in msgs
    /\ m.type = "phase1"
    /\ loc[p] = "wait1"
    /\ m.sender \notin { s \in Proc : \E mm \in rcv[p] : mm = m }
    /\ rcv' = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ UNCHANGED << loc, prop, est, dec, msgs, crashCount >>

ReadyForPhase2(p) ==
    /\ loc[p] = "wait1"
    /\ Cardinality(ReceivedPhase1(p)) >= N - T
    /\ est' = [est EXCEPT ![p] = MaxInView(p)]
    /\ loc' = [loc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED << view, prop, dec, msgs, rcv, crashCount >>

\* ======================================================================
\*   Phase‑2 actions
\* ======================================================================
BroadcastPhase2(p) ==
    /\ loc[p] = "bcast2"
    /\ LET m == [type |-> "phase2",
                sender |-> p,
                value  |-> prop[p],
                est    |-> est[p]] IN
       msgs' = msgs \cup {m}
    /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED << view, prop, est, dec, rcv, crashCount >>

ReceivePhase2(p, m) ==
    /\ m \in msgs
    /\ m.type = "phase2"
    /\ loc[p] = "wait2"
    /\ m.sender \notin { s \in Proc : \E mm \in rcv[p] : mm = m }
    /\ rcv' = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
    /\ UNCHANGED << loc, view, prop, est, dec, msgs, crashCount >>

Decide(p) ==
    /\ loc[p] = "wait2"
    /\ \E v \in Values :
         Cardinality({ m \in ReceivedPhase2(p) : m.est = v }) >= N - T
    /\ LET v == CHOOSE w \in Values :
                 Cardinality({ m \in ReceivedPhase2(p) : m.est = w }) >= N - T
       IN
          /\ dec' = [dec EXCEPT ![p] = v]
          /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, msgs, rcv, crashCount >>

Choose(p) ==
    /\ loc[p] = "wait2"
    /\ Cardinality({ m \in msgs : m.type = "phase2" }) = N
    /\ \A v \in Values :
         Cardinality({ m \in ReceivedPhase2(p) : m.est = v }) < N - T
    /\ \E v \in Values :
         v \in { view[p][q] : q \in Proc }
    /\ LET v == CHOOSE w \in Values :
                 w \in { view[p][q] : q \in Proc }
       IN
          /\ dec' = [dec EXCEPT ![p] = v]
          /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, msgs, rcv, crashCount >>

\* ======================================================================
\*   Crash action
\* ======================================================================
Crash(p) ==
    /\ loc[p] # "crashed"
    /\ crashCount < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashCount' = crashCount + 1
    /\ UNCHANGED << view, prop, est, dec, msgs, rcv >>

\* ======================================================================
\*   Next-state relation
\* ======================================================================
Next ==
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc : \E m \in msgs : ReceivePhase1(p, m)
    \/ \E p \in Proc : ReadyForPhase2(p)
    \/ \E p \in Proc : BroadcastPhase2(p)
    \/ \E p \in Proc : \E m \in msgs : ReceivePhase2(p, m)
    \/ \E p \in Proc : Decide(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Crash(p)

\* ======================================================================
\*   Specification
\* ======================================================================
Spec == Init /\ [][Next]_vars

\* ======================================================================
\*   Type correctness invariant
\* ======================================================================
TypeOK ==
    /\ loc \in [Proc -> LocSet]
    /\ view \in [Proc -> [Proc -> Values \cup {Bottom}]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ dec \in [Proc -> (Values \cup {Bottom})]
    /\ msgs \subseteq Message
    /\ rcv \in [Proc -> SUBSET Message]
    /\ crashCount \in Nat
    /\ crashCount <= F

\* ======================================================================
\*   Safety invariants
\* ======================================================================
Validity ==
    \A p \in Proc :
        dec[p] # Bottom =>
            /\ dec[p] \in Values
            /\ \E q \in Proc : prop[q] = dec[p]

Agreement ==
    \A p, q \in Proc :
        /\ dec[p] # Bottom /\ dec[q] # Bottom
        => dec[p] = dec[q]

\* ======================================================================
\*   The names required by the .cfg file
\* ======================================================================
SPEC == Spec

INVARS == TypeOK /\ Validity /\ Agreement

====