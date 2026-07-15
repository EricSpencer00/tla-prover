---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    N,          \* Number of processes
    T,          \* Maximum number of tolerated faults
    F,          \* Upper bound on actual crash faults
    Values,     \* Finite totally ordered set of proposal values
    Bottom      \* Special bottom value not in Values

\* ----------------------------------------------------------------------
\* Basic definitions
\* ----------------------------------------------------------------------
Proc == 1..N
Value == Values \cup {Bottom}
MessageType == {"phase1", "phase2"}

Message == [type : MessageType,
            sender : Proc,
            prop   : Value,
            est    : Value]  \* For phase1, est = Bottom

LOCATIONS == {"broadcast1", "wait1",
              "broadcast2", "wait2",
              "choosing", "done", "crashed"}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    loc,        \* [Proc -> location]
    prop,       \* [Proc -> Value]    proposed values
    est,        \* [Proc -> Value]    estimated values (Bottom until computed)
    decision,   \* [Proc -> Value]    decided value (Bottom until decided)
    localView,  \* [Proc -> [Proc -> Value]]   matrix of received values
    sent,       \* Set of messages that have been broadcast
    recv        \* [Proc -> SUBSET Message]    messages each proc has received
    crashedCnt  \* Number of processes that have crashed

vars == <<loc, prop, est, decision, localView, sent, recv, crashedCnt>>

\* ----------------------------------------------------------------------
\* Type correctness predicate (used for TypeOK)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ loc \in [Proc -> LOCATIONS]
    /\ prop \in [Proc -> Value]
    /\ est \in [Proc -> Value]
    /\ decision \in [Proc -> Value]
    /\ localView \in [Proc -> [Proc -> Value]]
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]
    /\ crashedCnt \in Nat
    /\ \A i \in Proc: recv[i] \subseteq sent
    /\ \A i \in Proc: crashedCnt = Cardinality({j \in Proc : loc[j] = "crashed"})

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Max(s) ==
    IF s = {} THEN Bottom
    ELSE CHOOSE x \in s : \A y \in s : y <= x

Quorum == N - T

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ loc = [i \in Proc |-> "broadcast1"]
    /\ prop \in [i \in Proc |-> Values] \* each process chooses any value from Values
    /\ est = [i \in Proc |-> Bottom]
    /\ decision = [i \in Proc |-> Bottom]
    /\ localView = [i \in Proc |-> [j \in Proc |-> Bottom]]
    /\ sent = {}
    /\ recv = [i \in Proc |-> {}]
    /\ crashedCnt = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
    /\ loc[p] = "broadcast1"
    /\ let m == [type |-> "phase1",
                sender |-> p,
                prop   |-> prop[p],
                est    |-> Bottom] in
       /\ sent' = sent \cup {m}
    /\ UNCHANGED <<loc, prop, est, decision, localView, recv, crashedCnt>>

MoveToWait1(p) ==
    /\ loc[p] = "broadcast1"
    /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<prop, est, decision, localView, sent, recv, crashedCnt>>

Receive1(p) ==
    /\ loc[p] = "wait1"
    /\ \E m \in sent :
          /\ m.type = "phase1"
          /\ m.sender \notin {j \in Proc : \E mm \in recv[p] : mm = m}
          /\ localView' = [localView EXCEPT ![p][m.sender] = m.prop]
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<loc, prop, est, decision, sent, crashedCnt>>

ComputeEst(p) ==
    /\ loc[p] = "wait1"
    /\ Cardinality({j \in Proc : localView[p][j] # Bottom}) >= Quorum
    /\ est' = [est EXCEPT ![p] = Max({localView[p][j] : j \in Proc})]
    /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
    /\ UNCHANGED <<prop, decision, localView, sent, recv, crashedCnt>>

Broadcast2(p) ==
    /\ loc[p] = "broadcast2"
    /\ let m == [type |-> "phase2",
                sender |-> p,
                prop   |-> prop[p],
                est    |-> est[p]] in
       /\ sent' = sent \cup {m}
    /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<prop, est, decision, localView, recv, crashedCnt>>

Receive2(p) ==
    /\ loc[p] = "wait2"
    /\ \E m \in sent :
          /\ m.type = "phase2"
          /\ m.sender \notin {j \in Proc : \E mm \in recv[p] : mm = m}
          /\ localView' = [localView EXCEPT ![p][m.sender] = m.est]
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<loc, prop, est, decision, sent, crashedCnt>>

DecideByThreshold(p) ==
    /\ loc[p] = "wait2"
    /\ \E v \in Values :
          Cardinality({m \in recv[p] : m.type = "phase2" /\ m.est = v}) >= Quorum
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<prop, est, localView, sent, recv, crashedCnt>>

MoveToChoosing(p) ==
    /\ loc[p] = "wait2"
    /\ Cardinality({m \in recv[p] : m.type = "phase2"}) = N
    /\ \A v \in Values :
          Cardinality({m \in recv[p] : m.type = "phase2" /\ m.est = v}) < Quorum
    /\ loc' = [loc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<prop, est, decision, localView, sent, recv, crashedCnt>>

ChooseAndDecide(p) ==
    /\ loc[p] = "choosing"
    /\ \E v \in Values :
          v \in {localView[p][j] : j \in Proc}
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<prop, est, localView, sent, recv, crashedCnt>>

Crash(p) ==
    /\ loc[p] # "crashed"
    /\ crashedCnt < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashedCnt' = crashedCnt + 1
    /\ UNCHANGED <<prop, est, decision, localView, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : Broadcast1(p)
    \/ \E p \in Proc : MoveToWait1(p)
    \/ \E p \in Proc : Receive1(p)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : Broadcast2(p)
    \/ \E p \in Proc : Receive2(p)
    \/ \E p \in Proc : DecideByThreshold(p)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : ChooseAndDecide(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        decision[p] # Bottom => decision[p] \in Values

Agreement ==
    \A p, q \in Proc :
        /\ decision[p] # Bottom
        /\ decision[q] # Bottom
        => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* The module ends here
\* ----------------------------------------------------------------------
====