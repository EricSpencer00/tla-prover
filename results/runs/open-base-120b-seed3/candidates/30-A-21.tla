---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Assumptions on the constants
\* ----------------------------------------------------------------------
ASSUME /\ 2 * T < N
       /\ 0 <= F
       /\ F <= T
       /\ N > 0
       /\ Bottom \\in Values \/ {Bottom}
       /\ Values # {} 
       /\ Bottom \\notin Values

\* ----------------------------------------------------------------------
\* Process identifiers
\* ----------------------------------------------------------------------
Proc == 1..N

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message == [type   : {"p1","p2"},
            sender : Proc,
            value  : Values,
            est    : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* control location of each process
          view,             \* N-by-N matrix of observed values
          prop,             \* proposed value of each process
          est,              \* estimated value after phase 1
          dec,              \* decision value (Bottom = not decided)
          crashedCount,     \* number of crashed processes
          sent,             \* set of all sent messages
          recv              \* messages received by each process

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
PcValues == {"b1", "w1", "b2", "w2", "done", "crashed", "choosing"}

Max(S) == IF S = {} THEN Bottom
          ELSE CHOOSE v \in S : \A w \in S : v >= w

Phase1Msg(p) == [type |-> "p1",
                 sender |-> p,
                 value |-> prop[p],
                 est |-> Bottom]

Phase2Msg(p) == [type |-> "p2",
                 sender |-> p,
                 value |-> prop[p],
                 est |-> est[p]]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "b1"]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ prop \in [Proc -> Values]               \* any proposal
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
    /\ pc[p] = "b1"
    /\ pc' = [pc EXCEPT ![p] = "w1"]
    /\ sent' = sent \cup { Phase1Msg(p) }
    /\ UNCHANGED <<view, prop, est, dec, crashedCount, recv>>

ReceivePhase1(p) ==
    /\ pc[p] = "w1"
    /\ \E m \in sent :
         /\ m.type = "p1"
         /\ view[p][m.sender] = Bottom
         /\ view' = [view EXCEPT ![p][m.sender] = m.value]
         /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, prop, est, dec, crashedCount, sent>>

TransitionToPhase2(p) ==
    /\ pc[p] = "w1"
    /\ Cardinality({ s \in Proc : view[p][s] # Bottom }) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "b2"]
    /\ est' = [est EXCEPT ![p] = Max({ view[p][s] : s \in Proc })]
    /\ UNCHANGED <<view, prop, dec, crashedCount, sent, recv>>

BroadcastPhase2(p) ==
    /\ pc[p] = "b2"
    /\ pc' = [pc EXCEPT ![p] = "w2"]
    /\ sent' = sent \cup { Phase2Msg(p) }
    /\ UNCHANGED <<view, prop, est, dec, crashedCount, recv>>

ReceivePhase2(p) ==
    /\ pc[p] = "w2"
    /\ \E m \in sent :
         /\ m.type = "p2"
         /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, view, prop, est, dec, crashedCount, sent>>

Decide(p) ==
    /\ pc[p] = "w2"
    /\ \E v \in Values :
         /\ Cardinality({ m \in recv[p] : m.type = "p2" /\ m.est = v }) >= N - T
    /\ dec' = [dec EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashedCount, sent, recv>>

Choose(p) ==
    /\ pc[p] = "w2"
    /\ \A v \in Values :
         Cardinality({ m \in recv[p] : m.type = "p2" /\ m.est = v }) < N - T
    /\ Cardinality({ m \in recv[p] : m.type = "p2" }) = N
    /\ \E v \in Values :
         /\ \E q \in Proc : view[p][q] = v
    /\ dec' = [dec EXCEPT ![p] = v]   \* deterministic choice (any such v)
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashedCount, sent, recv>>

Crash(p) ==
    /\ crashedCount < F
    /\ pc[p] # "crashed"
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED <<view, prop, est, dec, sent, recv>>

Next ==
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc : ReceivePhase1(p)
    \/ \E p \in Proc : TransitionToPhase2(p)
    \/ \E p \in Proc : BroadcastPhase2(p)
    \/ \E p \in Proc : ReceivePhase2(p)
    \/ \E p \in Proc : Decide(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Crash(p)

vars == <<pc, view, prop, est, dec, crashedCount, sent, recv>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> PcValues]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ dec \in [Proc -> (Values \cup {Bottom})]
    /\ crashedCount \in Nat
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        dec[p] # Bottom => \E q \in Proc : prop[q] = dec[p]

Agreement ==
    \A p, q \in Proc :
        /\ dec[p] # Bottom
        /\ dec[q] # Bottom
        => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* Exported identifiers
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

====