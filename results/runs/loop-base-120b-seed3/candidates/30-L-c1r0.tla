---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Process identifiers
\* ----------------------------------------------------------------------
Proc == 1..N

\* ----------------------------------------------------------------------
\* Control locations
\* ----------------------------------------------------------------------
PCs == {"b1", "w1", "b2", "w2", "choose", "done", "crashed"}

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message == [type : {"p1","p2"},
            val  : Values,
            sender : Proc,
            est  : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc,                 \* [p \in Proc -> PC]
          view,               \* [p \in Proc -> [q \in Proc -> Values \cup {Bottom}]]
          propose,            \* [p \in Proc -> Values]
          est,                \* [p \in Proc -> Values \cup {Bottom}]
          dec,                \* [p \in Proc -> Values \cup {Bottom}]
          crashed,            \* Nat
          msgs,               \* SUBSET Message
          rcvEst              \* [p \in Proc -> [q \in Proc -> Values \cup {Bottom}]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* maximum of a non‑empty set of values (Values are totally ordered)
Max(S) == 
    IF S = {} THEN Bottom 
    ELSE CHOOSE v \in S : \A w \in S : v >= w

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> PCs]
    /\ view \in [Proc -> [Proc -> Values \cup {Bottom}]]
    /\ propose \in [Proc -> Values]
    /\ est \in [Proc -> Values \cup {Bottom}]
    /\ dec \in [Proc -> Values \cup {Bottom}]
    /\ crashed \in Nat
    /\ msgs \subseteq Message
    /\ rcvEst \in [Proc -> [Proc -> Values \cup {Bottom}]]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "b1"]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ propose = [p \in Proc |-> CHOOSE v \in Values : TRUE]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashed = 0
    /\ msgs = {}
    /\ rcvEst = [p \in Proc |-> [q \in Proc |-> Bottom]]

\* ----------------------------------------------------------------------
\* Phase‑1 broadcast
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
    /\ pc[p] = "b1"
    /\ pc' = [pc EXCEPT ![p] = "w1"]
    /\ msgs' = msgs \cup { [type |-> "p1",
                           val  |-> propose[p],
                           sender|-> p,
                           est  |-> Bottom] }
    /\ UNCHANGED <<view, propose, est, dec, crashed, rcvEst>>

\* ----------------------------------------------------------------------
\* Phase‑1 receive
\* ----------------------------------------------------------------------
ReceivePhase1(p, m) ==
    /\ pc[p] = "w1"
    /\ m \in msgs
    /\ m.type = "p1"
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<pc, propose, est, dec, crashed, rcvEst>>

\* ----------------------------------------------------------------------
\* Compute estimated value after enough phase‑1 messages
\* ----------------------------------------------------------------------
ComputeEst(p) ==
    LET recvVals == { view[p][q] : q \in Proc }
        knownVals == recvVals \ {Bottom}
    IN
    /\ pc[p] = "w1"
    /\ Cardinality({ q \in Proc : view[p][q] # Bottom }) >= N - T
    /\ est' = [est EXCEPT ![p] = Max(knownVals)]
    /\ pc' = [pc EXCEPT ![p] = "b2"]
    /\ UNCHANGED <<view, propose, dec, crashed, msgs, rcvEst>>

\* ----------------------------------------------------------------------
\* Phase‑2 broadcast
\* ----------------------------------------------------------------------
BroadcastPhase2(p) ==
    /\ pc[p] = "b2"
    /\ pc' = [pc EXCEPT ![p] = "w2"]
    /\ msgs' = msgs \cup { [type |-> "p2",
                           val  |-> propose[p],
                           sender|-> p,
                           est  |-> est[p]] }
    /\ UNCHANGED <<view, propose, est, dec, crashed, rcvEst>>

\* ----------------------------------------------------------------------
\* Phase‑2 receive
\* ----------------------------------------------------------------------
ReceivePhase2(p, m) ==
    /\ pc[p] = "w2"
    /\ m \in msgs
    /\ m.type = "p2"
    /\ rcvEst' = [rcvEst EXCEPT ![p][m.sender] = m.est]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<pc, view, propose, est, dec, crashed>>

\* ----------------------------------------------------------------------
\* Decision when a value appears from at least N‑T processes
\* ----------------------------------------------------------------------
DecideIfThreshold(p) ==
    LET counts == [v \in Values |-> Cardinality({ q \in Proc : rcvEst[p][q] = v })]
        goodVals == { v \in Values : counts[v] >= N - T }
    IN
    /\ pc[p] = "w2"
    /\ goodVals # {}
    /\ LET v == CHOOSE w \in goodVals : TRUE
       IN /\ dec' = [dec EXCEPT ![p] = v]
          /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, propose, est, crashed, msgs, rcvEst>>

\* ----------------------------------------------------------------------
\* Move to choosing state when all N phase‑2 messages are received
\* but no value reaches the threshold
\* ----------------------------------------------------------------------
AllReceivedNoThreshold(p) ==
    /\ pc[p] = "w2"
    /\ \A q \in Proc : rcvEst[p][q] # Bottom   \* all N messages received
    /\ \A v \in Values : Cardinality({ q \in Proc : rcvEst[p][q] = v }) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<view, propose, est, dec, crashed, msgs, rcvEst>>

\* ----------------------------------------------------------------------
\* Deterministic choosing from the local view
\* ----------------------------------------------------------------------
Choose(p) ==
    /\ pc[p] = "choose"
    /\ \E v \in Values : \E q \in Proc : view[p][q] = v
    /\ LET v == CHOOSE w \in Values : \E q \in Proc : view[p][q] = w
       IN /\ dec' = [dec EXCEPT ![p] = v]
          /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, propose, est, crashed, msgs, rcvEst>>

\* ----------------------------------------------------------------------
\* Crash a process (if fewer than F have crashed so far)
\* ----------------------------------------------------------------------
Crash(p) ==
    /\ pc[p] # "crashed"
    /\ crashed < F
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, propose, est, dec, msgs, rcvEst>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc, m \in msgs : ReceivePhase1(p, m)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : BroadcastPhase2(p)
    \/ \E p \in Proc, m \in msgs : ReceivePhase2(p, m)
    \/ \E p \in Proc : DecideIfThreshold(p)
    \/ \E p \in Proc : AllReceivedNoThreshold(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<pc, view, propose, est, dec, crashed, msgs, rcvEst>>

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc : dec[p] # Bottom => dec[p] \in Values

Agreement ==
    \A p, q \in Proc :
        /\ dec[p] # Bottom
        /\ dec[q] # Bottom
        => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* The set of invariants required by the cfg file
\* ----------------------------------------------------------------------
THEOREM TypeOKInv == Spec => []TypeOK
THEOREM ValidityInv == Spec => []Validity
THEOREM AgreementInv == Spec => []Agreement

=============================================================================