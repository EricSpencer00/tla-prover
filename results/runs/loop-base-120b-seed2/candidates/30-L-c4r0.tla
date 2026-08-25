---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Basic sets
\* ----------------------------------------------------------------------
Proc == 1..N
Loc  == {"b1", "w1", "b2", "w2", "done", "crashed", "choosing"}
MsgType == {"phase1", "phase2"}
Value == Values \cup {Bottom}

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message ==
    [type : MsgType,
     sender : Proc,
     v : Value,
     e : Value]   \* for phase1 messages e = Bottom

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES loc, view, prop, est, dec, crashedCount, sent, received

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* maximum of a non‑empty set of totally ordered values
MaxVal(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE x \in S :
            \A y \in S : y <= x

\* set of messages of a given type received by p
MsgsOfType(p, t) == { m \in received[p] : m.type = t }

\* number of distinct senders from which p has a non‑bottom view entry
KnownSenders(p) == { s \in Proc : view[p][s] # Bottom }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ loc = [p \in Proc |-> "b1"]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ prop \in [Proc -> Value] /\ \A p \in Proc : prop[p] \in Values
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ received = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
    /\ loc[p] = "b1"
    /\ UNCHANGED <<view, prop, est, dec, crashedCount, received>>
    /\ sent' = sent \cup {
            [type |-> "phase1",
             sender |-> p,
             v |-> prop[p],
             e |-> Bottom]
        }
    /\ loc' = [loc EXCEPT ![p] = "w1"]

ReceivePhase1(p, m) ==
    /\ m \in sent
    /\ m.type = "phase1"
    /\ loc[p] = "w1"
    /\ UNCHANGED <<prop, est, dec, crashedCount, sent>>
    /\ view' = [view EXCEPT ![p][m.sender] = m.v]
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ loc' = loc

ComputeEst(p) ==
    /\ loc[p] = "w1"
    /\ Cardinality(KnownSenders(p)) >= N - T
    /\ UNCHANGED <<view, prop, dec, crashedCount, sent, received>>
    /\ est' = [est EXCEPT ![p] = MaxVal({ view[p][s] : s \in Proc })]
    /\ loc' = [loc EXCEPT ![p] = "b2"]

BroadcastPhase2(p) ==
    /\ loc[p] = "b2"
    /\ UNCHANGED <<view, prop, est, dec, crashedCount, received>>
    /\ sent' = sent \cup {
            [type |-> "phase2",
             sender |-> p,
             v |-> prop[p],
             e |-> est[p]]
        }
    /\ loc' = [loc EXCEPT ![p] = "w2"]

ReceivePhase2(p, m) ==
    /\ m \in sent
    /\ m.type = "phase2"
    /\ loc[p] = "w2"
    /\ UNCHANGED <<prop, est, dec, crashedCount, sent, loc>>
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ view' = view    \* (optional: could store m.v again, kept unchanged)

Decide(p) ==
    /\ loc[p] = "w2"
    /\ \E val \in Values :
          Cardinality({ m \in received[p] :
                         m.type = "phase2" /\ m.e = val }) >= N - T
    /\ LET val == CHOOSE v \in Values :
                Cardinality({ m \in received[p] :
                                 m.type = "phase2" /\ m.e = v }) >= N - T
       IN TRUE
    /\ UNCHANGED <<view, prop, est, crashedCount, sent, received>>
    /\ dec' = [dec EXCEPT ![p] = val]
    /\ loc' = [loc EXCEPT ![p] = "done"]

Choose(p) ==
    /\ loc[p] = "w2"
    /\ Cardinality({ m \in received[p] : m.type = "phase2" }) = N
    /\ \A v \in Values :
          Cardinality({ m \in received[p] :
                         m.type = "phase2" /\ m.e = v }) < N - T
    /\ \E v \in Values : \E s \in Proc : view[p][s] = v
    /\ LET chosen == CHOOSE v \in Values :
                \E s \in Proc : view[p][s] = v
       IN TRUE
    /\ UNCHANGED <<view, prop, est, crashedCount, sent, received>>
    /\ dec' = [dec EXCEPT ![p] = chosen]
    /\ loc' = [loc EXCEPT ![p] = "done"]

Crash(p) ==
    /\ crashedCount < F
    /\ loc[p] # "crashed"
    /\ UNCHANGED <<view, prop, est, dec, sent, received>>
    /\ crashedCount' = crashedCount + 1
    /\ loc' = [loc EXCEPT ![p] = "crashed"]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc, m \in Message : ReceivePhase1(p, m)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : BroadcastPhase2(p)
    \/ \E p \in Proc, m \in Message : ReceivePhase2(p, m)
    \/ \E p \in Proc : Decide(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<loc, view, prop, est, dec, crashedCount, sent, received>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ loc \in [Proc -> Loc]
    /\ view \in [Proc -> [Proc -> Value]]
    /\ prop \in [Proc -> Value] /\ \A p \in Proc : prop[p] \in Values
    /\ est \in [Proc -> Value]
    /\ dec \in [Proc -> Value]
    /\ crashedCount \in Nat
    /\ sent \subseteq Message
    /\ received \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        /\ dec[p] # Bottom
        => /\ dec[p] \in Values
           /\ \E q \in Proc : prop[q] = dec[p]

Agreement ==
    \A p, q \in Proc :
        (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

=============================================================================