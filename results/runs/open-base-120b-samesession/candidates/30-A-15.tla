---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    N,          \* number of processes
    T,          \* tolerance parameter (2*T < N)
    F,          \* maximum actual crash faults (0 <= F <= T)
    Values,     \* finite totally ordered set of proposal values
    Bottom      \* special value not in Values

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Proc == 1..N

\* Total order on Values is assumed to be the natural order (e.g., if Values
\* are numbers).  For a generic totally ordered set one could add a constant
\* `Le` and assume it is a total order; here we simply reuse `<=` which is
\* defined for numbers.  The spec works for any Values that are a subset of
\* Nat.
\* ----------------------------------------------------------------------
MaxVal(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE v \in S: \A w \in S : w <= v

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Msg ==
    [type : {"ph1", "ph2"},
     val  : Values,
     sender: Proc,
     est  : Values \cup {Bottom}]  \* `est` is meaningful only for phase‑2 msgs

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    pc,         \* [Proc -> {"b1","w1","b2","w2","done","crashed","choosing"}]
    view,       \* [Proc -> [Proc -> Values \cup {Bottom}]]
    prop,       \* [Proc -> Values]            \* initial proposals
    est,        \* [Proc -> Values \cup {Bottom}]
    dec,        \* [Proc -> Values \cup {Bottom}]
    crashedSet, \* SUBSET Proc
    msgs,       \* SUBSET Msg
    rcv         \* [Proc -> SUBSET Msg]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "b1"]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ prop \in [Proc -> Values]          \* arbitrary initial proposals
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashedSet = {} 
    /\ msgs = {}
    /\ rcv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
    /\ pc[p] = "b1"
    /\ p \notin crashedSet
    /\ LET m == [type |-> "ph1", val |-> prop[p], sender |-> p, est |-> Bottom] IN
       msgs' = msgs \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "w1"]
    /\ UNCHANGED << view, prop, est, dec, crashedSet, rcv >>

ReceivePhase1(p, m) ==
    /\ pc[p] = "w1"
    /\ p \notin crashedSet
    /\ m \in msgs
    /\ m.type = "ph1"
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ rcv' = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
    /\ UNCHANGED << pc, prop, est, dec, crashedSet, msgs >>

Phase1Transition(p) ==
    /\ pc[p] = "w1"
    /\ p \notin crashedSet
    /\ LET received == {s \in Proc : view[p][s] # Bottom} IN
       Cardinality(received) >= N - T
    /\ est' = [est EXCEPT ![p] = MaxVal({view[p][s] : s \in Proc})]
    /\ pc' = [pc EXCEPT ![p] = "b2"]
    /\ UNCHANGED << view, prop, dec, crashedSet, msgs, rcv >>

BroadcastPhase2(p) ==
    /\ pc[p] = "b2"
    /\ p \notin crashedSet
    /\ LET m == [type |-> "ph2",
                 val  |-> prop[p],
                 sender |-> p,
                 est  |-> est[p]] IN
       msgs' = msgs \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "w2"]
    /\ UNCHANGED << view, prop, est, dec, crashedSet, rcv >>

ReceivePhase2(p, m) ==
    /\ pc[p] = "w2"
    /\ p \notin crashedSet
    /\ m \in msgs
    /\ m.type = "ph2"
    /\ rcv' = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
    /\ UNCHANGED << pc, view, prop, est, dec, crashedSet, msgs >>

DecideFromEst(p) ==
    /\ pc[p] = "w2"
    /\ p \notin crashedSet
    /\ \E v \in Values :
          Cardinality({m \in rcv[p] : m.type = "ph2" /\ m.est = v}) >= N - T
    /\ LET v == CHOOSE v \in Values :
            Cardinality({m \in rcv[p] : m.type = "ph2" /\ m.est = v}) >= N - T
       IN
       /\ dec' = [dec EXCEPT ![p] = v]
       /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashedSet, msgs, rcv >>

MoveToChoosing(p) ==
    /\ pc[p] = "w2"
    /\ p \notin crashedSet
    /\ Cardinality({m \in rcv[p] : m.type = "ph2"}) = N
    /\ \A v \in Values :
          Cardinality({m \in rcv[p] : m.type = "ph2" /\ m.est = v}) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED << view, prop, est, dec, crashedSet, msgs, rcv >>

ChooseAndDecide(p) ==
    /\ pc[p] = "choosing"
    /\ p \notin crashedSet
    /\ LET candidates == {view[p][s] : s \in Proc /\ view[p][s] # Bottom}
           IN candidates = candidates \/ {prop[p]}
       /\ candidates # {}
       /\ LET v == CHOOSE x \in candidates : TRUE IN
          /\ dec' = [dec EXCEPT ![p] = v]
          /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashedSet, msgs, rcv >>

Crash(p) ==
    /\ p \notin crashedSet
    /\ Cardinality(crashedSet) < F
    /\ crashedSet' = crashedSet \cup {p}
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ UNCHANGED << view, prop, est, dec, msgs, rcv >>

\* ----------------------------------------------------------------------
\* Next relation (disjunction of all possible steps)
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc, m \in Msg : ReceivePhase1(p, m)
    \/ \E p \in Proc : Phase1Transition(p)
    \/ \E p \in Proc : BroadcastPhase2(p)
    \/ \E p \in Proc, m \in Msg : ReceivePhase2(p, m)
    \/ \E p \in Proc : DecideFromEst(p)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : ChooseAndDecide(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< pc, view, prop, est, dec, crashedSet, msgs, rcv >>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> {"b1","w1","b2","w2","done","crashed","choosing"}]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ dec \in [Proc -> (Values \cup {Bottom})]
    /\ crashedSet \subseteq Proc
    /\ msgs \subseteq Msg
    /\ rcv \in [Proc -> SUBSET Msg]

Validity ==
    \A p \in Proc : dec[p] # Bottom => dec[p] \in Values

Agreement ==
    \A p , q \in Proc :
        (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====