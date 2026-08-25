---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Types and helper definitions
\* ----------------------------------------------------------------------
ProcessSet == 1..N

PcValues == {"b1", "w1", "b2", "w2", "done", "crashed", "choosing"}

Message == [type : {"p1", "p2"},
            sender : ProcessSet,
            val    : Values,
            est    : Values \cup {Bottom}]

\* Maximum of a non‑empty set of totally ordered values
MaxVal(S) == CHOOSE v \in S : \A w \in S : w <= v

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc, prop, view, est, decision, crashedCount, sent, recv

vars == << pc, prop, view, est, decision, crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [i \in ProcessSet |-> "b1"]
    /\ prop \in [ProcessSet -> Values]                \* each process chooses a proposal
    /\ view = [i \in ProcessSet |-> [j \in ProcessSet |-> Bottom]]
    /\ est = [i \in ProcessSet |-> Bottom]
    /\ decision = [i \in ProcessSet |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = [i \in ProcessSet |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(i) ==
    /\ pc[i] = "b1"
    /\ let m == [type |-> "p1", sender |-> i, val |-> prop[i], est |-> Bottom] in
       /\ sent' = sent \cup {m}
       /\ pc'   = [pc EXCEPT ![i] = "w1"]
    /\ UNCHANGED << prop, view, est, decision, recv, crashedCount >>

ReceivePhase1(i, m) ==
    /\ pc[i] = "w1"
    /\ m \in sent
    /\ m.type = "p1"
    /\ \A r \in recv[i] : r.sender # m.sender          \* not already received from this sender
    /\ view' = [view EXCEPT ![i][m.sender] = m.val]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED << pc, prop, est, decision, sent, crashedCount >>

ComputeEst(i) ==
    /\ pc[i] = "w1"
    /\ Cardinality({j \in ProcessSet : view[i][j] # Bottom}) >= N - T
    /\ LET vals == { view[i][j] : j \in ProcessSet /\ view[i][j] # Bottom } IN
          maxV == MaxVal(vals)
    IN
       /\ est' = [est EXCEPT ![i] = maxV]
       /\ pc'  = [pc EXCEPT ![i] = "b2"]
    /\ UNCHANGED << prop, view, decision, sent, recv, crashedCount >>

BroadcastPhase2(i) ==
    /\ pc[i] = "b2"
    /\ let m == [type |-> "p2", sender |-> i, val |-> prop[i], est |-> est[i]] in
       /\ sent' = sent \cup {m}
       /\ pc'   = [pc EXCEPT ![i] = "w2"]
    /\ UNCHANGED << prop, view, est, decision, recv, crashedCount >>

ReceivePhase2(i, m) ==
    /\ pc[i] = "w2"
    /\ m \in sent
    /\ m.type = "p2"
    /\ \A r \in recv[i] : r.sender # m.sender          \* not already received from this sender
    /\ view' = [view EXCEPT ![i][m.sender] = m.est]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED << pc, prop, est, decision, sent, crashedCount >>

Decide(i) ==
    /\ pc[i] = "w2"
    /\ \E v \in Values :
          Cardinality({m \in recv[i] : m.type = "p2" /\ m.est = v}) >= N - T
    /\ LET v == CHOOSE w \in Values :
                Cardinality({m \in recv[i] : m.type = "p2" /\ m.est = w}) >= N - T
    IN
       /\ decision' = [decision EXCEPT ![i] = v]
       /\ pc'       = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED << prop, view, est, sent, recv, crashedCount >>

MoveToChoosing(i) ==
    /\ pc[i] = "w2"
    /\ Cardinality({ m.sender : m \in recv[i] }) = N
    /\ \A v \in Values :
          Cardinality({m \in recv[i] : m.type = "p2" /\ m.est = v}) < N - T
    /\ pc' = [pc EXCEPT ![i] = "choosing"]
    /\ UNCHANGED << prop, view, est, decision, sent, recv, crashedCount >>

Choose(i) ==
    /\ pc[i] = "choosing"
    /\ LET vals == { view[i][j] : j \in ProcessSet /\ view[i][j] # Bottom } IN
          vals # {}
    IN
       /\ decision' = [decision EXCEPT ![i] = CHOOSE x \in vals : TRUE]
       /\ pc'       = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED << prop, view, est, sent, recv, crashedCount >>

Crash(i) ==
    /\ pc[i] # "crashed"
    /\ crashedCount < F
    /\ pc' = [pc EXCEPT ![i] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED << prop, view, est, decision, sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E i \in ProcessSet : BroadcastPhase1(i)
    \/ \E i \in ProcessSet, m \in Message : ReceivePhase1(i, m)
    \/ \E i \in ProcessSet : ComputeEst(i)
    \/ \E i \in ProcessSet : BroadcastPhase2(i)
    \/ \E i \in ProcessSet, m \in Message : ReceivePhase2(i, m)
    \/ \E i \in ProcessSet : Decide(i)
    \/ \E i \in ProcessSet : MoveToChoosing(i)
    \/ \E i \in ProcessSet : Choose(i)
    \/ \E i \in ProcessSet : Crash(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [ProcessSet -> PcValues]
    /\ prop \in [ProcessSet -> Values]
    /\ view \in [ProcessSet -> [ProcessSet -> Values \cup {Bottom}]]
    /\ est \in [ProcessSet -> Values \cup {Bottom}]
    /\ decision \in [ProcessSet -> Values \cup {Bottom}]
    /\ crashedCount \in Nat
    /\ sent \subseteq Message
    /\ recv \in [ProcessSet -> SUBSET Message]

Validity ==
    \A i \in ProcessSet :
        decision[i] # Bottom =>
            /\ decision[i] \in Values
            /\ \E j \in ProcessSet : decision[i] = prop[j]

Agreement ==
    \A i, j \in ProcessSet :
        (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

\* ----------------------------------------------------------------------
\* The required identifiers for the configuration file
\* ----------------------------------------------------------------------
\* SPECIFICATION formula
\* INVARIANTS
\* (they are already defined with the exact names)

====