---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Process set
\* ----------------------------------------------------------------------
Proc == 1 .. N

\* ----------------------------------------------------------------------
\* Control locations
\* ----------------------------------------------------------------------
Locs == {"bcast1", "wait1", "bcast2", "wait2", "choosing", "done", "crashed"}

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message == 
    { [type |-> 1, sender |-> p, val |-> v] :
        p \in Proc, v \in Values } \cup
    { [type |-> 2, sender |-> p, val |-> v, estVal |-> e] :
        p \in Proc, v \in Values, e \in Values \cup {Bottom} }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pc, view, prop, est, decision, crashed, msgs, recv

vars == << pc, view, prop, est, decision, crashed, msgs, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MaxVal(S) ==
    IF S = {} THEN Bottom
    ELSE
        CHOOSE x \in S : \A y \in S : y <= x

\* ----------------------------------------------------------------------
\* Type correctness
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> Locs]
    /\ view \in [Proc -> [Proc -> Values \cup {Bottom}]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> Values \cup {Bottom}]
    /\ decision \in [Proc -> Values \cup {Bottom}]
    /\ crashed \in Nat
    /\ msgs \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "bcast1"]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ prop = [p \in Proc |-> CHOOSE v \in Values : TRUE]
    /\ est = [p \in Proc |-> Bottom]
    /\ decision = [p \in Proc |-> Bottom]
    /\ crashed = 0
    /\ msgs = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
    /\ pc[p] = "bcast1"
    /\ msgs' = msgs \cup {[type |-> 1, sender |-> p, val |-> prop[p]]}
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED << view, prop, est, decision, crashed, recv >>

Receive1(p, m) ==
    /\ pc[p] = "wait1"
    /\ m \in msgs
    /\ m.type = 1
    /\ let s == m.sender in
       view' = [view EXCEPT ![p][s] = m.val]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << pc, prop, est, decision, crashed, msgs >>

ComputeEst(p) ==
    /\ pc[p] = "wait1"
    /\ Cardinality({ m \in recv[p] : m.type = 1 }) >= N - T
    /\ est' = [est EXCEPT ![p] = MaxVal({ view[p][q] : q \in Proc })]
    /\ pc' = [pc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED << view, prop, decision, crashed, msgs, recv >>

Broadcast2(p) ==
    /\ pc[p] = "bcast2"
    /\ msgs' = msgs \cup {[type |-> 2, sender |-> p,
                         val |-> prop[p], estVal |-> est[p]]}
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED << view, prop, est, decision, crashed, recv >>

Receive2(p, m) ==
    /\ pc[p] = "wait2"
    /\ m \in msgs
    /\ m.type = 2
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << pc, view, prop, est, decision, crashed, msgs >>

Decide(p) ==
    /\ pc[p] = "wait2"
    /\ LET estVals == { m.estVal : m \in recv[p] /\ m.type = 2 } IN
       \E v \in estVals :
          Cardinality({ m \in recv[p] :
                        m.type = 2 /\ m.estVal = v }) >= N - T
    /\ LET chosen == 
          CHOOSE v \in estVals :
              Cardinality({ m \in recv[p] :
                             m.type = 2 /\ m.estVal = v }) >= N - T
       IN
       decision' = [decision EXCEPT ![p] = chosen]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashed, msgs, recv >>

MoveToChoosing(p) ==
    /\ pc[p] = "wait2"
    /\ Cardinality({ m \in recv[p] : m.type = 2 }) = N
    /\ \A v \in Values :
          Cardinality({ m \in recv[p] :
                         m.type = 2 /\ m.estVal = v }) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED << view, prop, est, decision, crashed, msgs, recv >>

Choose(p) ==
    /\ pc[p] = "choosing"
    /\ LET appeared == { view[p][q] : q \in Proc } IN
       decision' = [decision EXCEPT ![p] = 
                     CHOOSE v \in Values : v \in appeared]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashed, msgs, recv >>

Crash(p) ==
    /\ crashed < F
    /\ pc[p] # "crashed"
    /\ crashed' = crashed + 1
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ UNCHANGED << view, prop, est, decision, msgs, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc :
        \/ Broadcast1(p)
        \/ Receive1(p, m)   \* m quantified inside
        \/ ComputeEst(p)
        \/ Broadcast2(p)
        \/ Receive2(p, m)   \* m quantified inside
        \/ Decide(p)
        \/ MoveToChoosing(p)
        \/ Choose(p)
        \/ Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        decision[p] # Bottom =>
            decision[p] \in { prop[q] : q \in Proc }

Agreement ==
    \A p, q \in Proc :
        /\ decision[p] # Bottom
        /\ decision[q] # Bottom
        => decision[p] = decision[q]

====