---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Basic assumptions
\* ----------------------------------------------------------------------
ASSUME 2 * T < N
ASSUME 0 <= F /\ F <= T
ASSUME N > 0
ASSUME Bottom \\in Values = FALSE
ASSUME Values \\subseteq Nat   \* we need a total order for Max

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Processes == 1 .. N

PhaseVals == {"b1", "w1", "p2", "b2", "w2", "done", "crashed", "choosing"}

MessageType == {"ph1", "ph2"}

Message ==
    [type : MessageType,
     value : Values,
     sender : Processes,
     est   : Values \cup {Bottom}]   \* for phase‑1 messages est = Bottom

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc, view, prop, est, dec, crashedCount, sent, rcv

vars == << pc, view, prop, est, dec, crashedCount, sent, rcv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MaxInView(p) ==
    LET vals == { view[p][q] : q \in Processes } \ {Bottom} IN
    IF vals = {} THEN Bottom
    ELSE CHOOSE v \in vals : \A w \in vals : w <= v

RecvSenders(p, typ) ==
    { m.sender : m \in rcv[p] /\ m.type = typ }

CountEst(p, v) ==
    Cardinality({ m \in rcv[p] : m.type = "ph2" /\ m.est = v })

AllSendersReceived(p) ==
    Cardinality({ m.sender : m \in rcv[p] }) = N

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Processes |-> "b1"]
    /\ prop = [p \in Processes |-> CHOOSE v \in Values : TRUE]
    /\ view = [p \in Processes |-> [q \in Processes |-> Bottom]]
    /\ est  = [p \in Processes |-> Bottom]
    /\ dec  = [p \in Processes |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ rcv = [p \in Processes |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Broadcast phase‑1
Broadcast1(p) ==
    /\ pc[p] = "b1"
    /\ sent' = sent \cup {
           [type |-> "ph1",
            value |-> prop[p],
            sender |-> p,
            est |-> Bottom]
         }
    /\ pc' = [pc EXCEPT ![p] = "w1"]
    /\ UNCHANGED << view, prop, est, dec, crashedCount, rcv >>

\* 2. Receive a phase‑1 message
Receive1(p, m) ==
    /\ pc[p] = "w1"
    /\ m \in sent
    /\ m.type = "ph1"
    /\ m \notin rcv[p]
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ rcv'  = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
    /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

\* 3. Compute estimate after enough phase‑1 messages
ComputeEst(p) ==
    /\ pc[p] = "w1"
    /\ Cardinality(RecvSenders(p, "ph1")) >= N - T
    /\ est' = [est EXCEPT ![p] = MaxInView(p)]
    /\ pc'  = [pc EXCEPT ![p] = "b2"]
    /\ UNCHANGED << view, prop, dec, crashedCount, sent, rcv >>

\* 4. Broadcast phase‑2
Broadcast2(p) ==
    /\ pc[p] = "b2"
    /\ sent' = sent \cup {
           [type |-> "ph2",
            value |-> prop[p],
            sender |-> p,
            est   |-> est[p]]
         }
    /\ pc' = [pc EXCEPT ![p] = "w2"]
    /\ UNCHANGED << view, prop, est, dec, crashedCount, rcv >>

\* 5. Receive a phase‑2 message
Receive2(p, m) ==
    /\ pc[p] = "w2"
    /\ m \in sent
    /\ m.type = "ph2"
    /\ m \notin rcv[p]
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ rcv'  = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
    /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

\* 6. Decide when a value appears in at least N‑T phase‑2 messages
Decide(p) ==
    /\ pc[p] = "w2"
    /\ \E v \in Values :
          CountEst(p, v) >= N - T
    /\ LET v == CHOOSE w \in Values : CountEst(p, w) >= N - T IN
       /\ dec' = [dec EXCEPT ![p] = v]
       /\ pc'  = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashedCount, sent, rcv >>

\* 7. Move to choosing when all N messages are received but no N‑T agreement
MoveToChoosing(p) ==
    /\ pc[p] = "w2"
    /\ \A v \in Values : CountEst(p, v) < N - T
    /\ AllSendersReceived(p)
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED << view, prop, est, dec, crashedCount, sent, rcv >>

\* 8. Choose a value from the local view and decide
Choose(p) ==
    /\ pc[p] = "choosing"
    /\ LET cand == { view[p][q] : q \in Processes /\ view[p][q] # Bottom } IN
       cand # {}
    /\ dec' = [dec EXCEPT ![p] = CHOOSE v \in cand : TRUE]
    /\ pc'  = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashedCount, sent, rcv >>

\* 9. Crash a process (subject to fault bound)
Crash(p) ==
    /\ crashedCount < F
    /\ pc[p] # "crashed"
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED << view, prop, est, dec, sent, rcv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Processes : Broadcast1(p)
    \/ \E p \in Processes : \E m \in sent : Receive1(p, m)
    \/ \E p \in Processes : ComputeEst(p)
    \/ \E p \in Processes : Broadcast2(p)
    \/ \E p \in Processes : \E m \in sent : Receive2(p, m)
    \/ \E p \in Processes : Decide(p)
    \/ \E p \in Processes : MoveToChoosing(p)
    \/ \E p \in Processes : Choose(p)
    \/ \E p \in Processes : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Processes -> PhaseVals]
    /\ view \in [Processes -> [Processes -> (Values \cup {Bottom})]]
    /\ prop \in [Processes -> Values]
    /\ est  \in [Processes -> (Values \cup {Bottom})]
    /\ dec  \in [Processes -> (Values \cup {Bottom})]
    /\ crashedCount \in Nat
    /\ sent \subseteq Message
    /\ rcv \in [Processes -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Processes :
        dec[p] # Bottom =>
          /\ dec[p] \in Values
          /\ \E q \in Processes : prop[q] = dec[p]

Agreement ==
    \A p, q \in Processes :
        (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* Exported identifiers
\* ----------------------------------------------------------------------
\* The cfg file expects the following names
\*   Spec, TypeOK, Validity, Agreement
\*   and the constants N, T, F, Values, Bottom
=============================================================================