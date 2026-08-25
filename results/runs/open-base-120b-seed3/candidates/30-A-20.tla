---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Assumptions on constants
\* ----------------------------------------------------------------------
ASSUME 2 * T < N
ASSUME 0 <= F /\ F <= T
ASSUME N > 0
ASSUME Bottom \notin Values

\* ----------------------------------------------------------------------
\* Basic definitions
\* ----------------------------------------------------------------------
Proc == 1 .. N

Loc == {"P1", "W1", "B2", "W2", "Done", "Choosing", "Crashed"}

Message == [type : {"p1", "p2"},
            sender : Proc,
            val    : Values \cup {Bottom},
            est    : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES phase, view, prop, est, decision, crashed, net, rec2

vars == << phase, view, prop, est, decision, crashed, net, rec2 >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ phase    = [p \in Proc |-> "P1"]
    /\ view     = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ prop \in [p \in Proc -> Values]          \* each process proposes a value
    /\ est      = [p \in Proc |-> Bottom]
    /\ decision = [p \in Proc |-> Bottom]
    /\ crashed  = {}
    /\ net      = {}
    /\ rec2     = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ReceivedSenders(p) == { q \in Proc : view[p][q] # Bottom }

ReceivedValues(p) ==
    { view[p][q] : q \in Proc } \cap Values

MaxOrBottom(S) ==
    IF S = {} THEN Bottom ELSE Max(S)

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastP1(p) ==
    /\ phase[p] = "P1"
    /\ phase' = [phase EXCEPT ![p] = "W1"]
    /\ net' = net \cup
              { [type |-> "p1",
                 sender |-> p,
                 val    |-> prop[p],
                 est    |-> Bottom] }
    /\ UNCHANGED << view, prop, est, decision, crashed, rec2 >>

ReceiveP1(p, m) ==
    /\ phase[p] = "W1"
    /\ m \in net
    /\ m.type = "p1"
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ net' = net \ {m}
    /\ UNCHANGED << phase, prop, est, decision, crashed, rec2 >>

ComputeEst(p) ==
    /\ phase[p] = "W1"
    /\ Cardinality(ReceivedSenders(p)) >= N - T
    /\ est' = [est EXCEPT ![p] = MaxOrBottom(ReceivedValues(p))]
    /\ phase' = [phase EXCEPT ![p] = "B2"]
    /\ UNCHANGED << view, prop, decision, crashed, net, rec2 >>

BroadcastP2(p) ==
    /\ phase[p] = "B2"
    /\ phase' = [phase EXCEPT ![p] = "W2"]
    /\ net' = net \cup
              { [type |-> "p2",
                 sender |-> p,
                 val    |-> prop[p],
                 est    |-> est[p]] }
    /\ UNCHANGED << view, prop, est, decision, crashed, rec2 >>

ReceiveP2(p, m) ==
    /\ phase[p] = "W2"
    /\ m \in net
    /\ m.type = "p2"
    /\ rec2' = [rec2 EXCEPT ![p] = rec2[p] \cup {m}]
    /\ net' = net \ {m}
    /\ UNCHANGED << phase, view, prop, est, decision, crashed >>

Decide(p) ==
    /\ phase[p] = "W2"
    /\ \E v \in Values :
          Cardinality({ m \in rec2[p] : m.est = v }) >= N - T
    /\ LET vChosen == 
            CHOOSE vv \in Values :
                Cardinality({ m \in rec2[p] : m.est = vv }) >= N - T
       IN TRUE
    /\ decision' = [decision EXCEPT ![p] = vChosen]
    /\ phase' = [phase EXCEPT ![p] = "Done"]
    /\ UNCHANGED << view, prop, est, crashed, net, rec2 >>

AllP2Received(p) == Cardinality(rec2[p]) = N

Choosing(p) ==
    /\ phase[p] = "W2"
    /\ AllP2Received(p)
    /\ \A v \in Values :
          Cardinality({ m \in rec2[p] : m.est = v }) < N - T
    /\ LET vals == ReceivedValues(p) IN
       vChosen == MaxOrBottom(vals)
    /\ decision' = [decision EXCEPT ![p] = vChosen]
    /\ phase' = [phase EXCEPT ![p] = "Done"]
    /\ UNCHANGED << view, prop, est, crashed, net, rec2 >>

Crash(p) ==
    /\ p \notin crashed
    /\ Cardinality(crashed) < F
    /\ crashed' = crashed \cup {p}
    /\ phase' = [phase EXCEPT ![p] = "Crashed"]
    /\ UNCHANGED << view, prop, est, decision, net, rec2 >>

Next ==
    \/ \E p \in Proc : BroadcastP1(p)
    \/ \E p \in Proc, m \in net : ReceiveP1(p, m)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : BroadcastP2(p)
    \/ \E p \in Proc, m \in net : ReceiveP2(p, m)
    \/ \E p \in Proc : Decide(p)
    \/ \E p \in Proc : Choosing(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ phase \in [Proc -> Loc]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ decision \in [Proc -> (Values \cup {Bottom})]
    /\ crashed \subseteq Proc
    /\ net \subseteq Message
    /\ rec2 \in [Proc -> SUBSET Message]
    /\ \A m \in net : m.type \in {"p1","p2"}
    /\ \A p \in Proc :
          (phase[p] = "Crashed") => p \in crashed

Validity ==
    \A p \in Proc :
        /\ decision[p] # Bottom
        => /\ decision[p] \in Values
           /\ \E q \in Proc : prop[q] = decision[p]

Agreement ==
    \A p, q \in Proc :
        /\ decision[p] # Bottom /\ decision[q] # Bottom
        => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* The required identifiers
\* ----------------------------------------------------------------------
\* SPECIFICATION formula
Spec == Spec

\* INVARIANTS
TypeOK == TypeOK
Validity == Validity
Agreement == Agreement

====