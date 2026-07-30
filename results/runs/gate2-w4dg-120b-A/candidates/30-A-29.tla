---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* The full set of messages, and the per-process received set, are tracked as
\* separate views of the same message pool.  This is intentional: the spec
\* counts a message as received once it appears in the per-process view, which
\* is how the "at least N-T distinct senders" condition is measured.
Messages == [tp: {"phase1", "phase2"}, val: Values \cup {Bottom},
             snd: 1..N, est: Values \cup {Bottom}]
RECURSIVE MaxIn(_, _)
MaxIn(S, f) == IF S = {} THEN Bottom
               ELSE LET x == CHOOSE y \in S : TRUE
                    IN IF f[x] > MaxIn(S \ {x}, f) THEN f[x] ELSE MaxIn(S \ {x}, f)

States == {"broadcast1", "wait1", "prepare", "broadcast2", "wait2",
           "done", "crashed", "choosing"}

VARIABLES phase, view, prop, estimate, decided, crashed, sent, recv

vars == <<phase, view, prop, estimate, decided, crashed, sent, recv>>

TypeOK ==
    /\ phase \in [1..N -> States]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ prop \in [1..N -> Values]
    /\ estimate \in [1..N -> Values \cup {Bottom}]
    /\ decided \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..F
    /\ sent \subseteq Messages
    /\ recv \in [1..N -> SUBSET Messages]

Init ==
    /\ phase = [p \in 1..N |-> "broadcast1"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ \E f \in [1..N -> Values]:
         prop = f
    /\ estimate = [p \in 1..N |-> Bottom]
    /\ decided = [p \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ recv = [p \in 1..N |-> {}]

BroadcastPhase1(p) ==
    /\ phase[p] = "broadcast1"
    /\ sent' = sent \cup
         { [tp |-> "phase1", val |-> prop[p], snd |-> p, est |-> Bottom] }
    /\ phase' = [phase EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<view, prop, estimate, decided, crashed, recv>>

Receive1(p, m) ==
    /\ phase[p] = "wait1"
    /\ m \in sent
    /\ m.tp = "phase1"
    /\ view[p][m.snd] = Bottom
    /\ view' = [view EXCEPT ![p][m.snd] = m.val]
    /\ recv' = [recv EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED <<phase, prop, estimate, decided, crashed, sent>>

ComputeEstimate(p) ==
    /\ phase[p] = "wait1"
    /\ Cardinality({q \in 1..N: view[p][q] # Bottom}) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = MaxIn(1..N, view[p])]
    /\ phase' = [phase EXCEPT ![p] = "broadcast2"]
    /\ UNCHANGED <<view, prop, decided, crashed, sent, recv>>

BroadcastPhase2(p) ==
    /\ phase[p] = "broadcast2"
    /\ sent' = sent \cup
         { [tp |-> "phase2", val |-> prop[p], snd |-> p, est |-> estimate[p]] }
    /\ phase' = [phase EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<view, prop, estimate, decided, crashed, recv>>

Receive2(p, m) ==
    /\ phase[p] = "wait2"
    /\ m \in sent
    /\ m.tp = "phase2"
    /\ view[p][m.snd] = Bottom
    /\ view' = [view EXCEPT ![p][m.snd] = m.val]
    /\ recv' = [recv EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED <<phase, prop, estimate, decided, crashed, sent>>

Decide(p) ==
    /\ phase[p] = "wait2"
    /\ \E v \in Values:
         /\ Cardinality({m \in recv[p]: m.tp = "phase2" /\ m.est = v}) >= N - T
         /\ decided' = [decided EXCEPT ![p] = v]
    /\ phase' = [phase EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

Choose(p) ==
    /\ phase[p] = "wait2"
    /\ \A m \in recv[p]: m.tp = "phase2"
    /\ phase[p] = "wait2"
    /\ \E v \in Values:
         /\ \E q \in 1..N: view[p][q] = v
         /\ decided' = [decided EXCEPT ![p] = v]
    /\ phase' = [phase EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

Crash(p) ==
    /\ phase[p] \in {"broadcast1", "wait1", "prepare", "broadcast2", "wait2"}
    /\ crashed < F
    /\ crashed' = crashed + 1
    /\ phase' = [phase EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<view, prop, estimate, decided, sent, recv>>

Next ==
    \/ \E p \in 1..N: BroadcastPhase1(p) \/ ComputeEstimate(p) \/ BroadcastPhase2(p)
                         \/ Decide(p) \/ Choose(p) \/ Crash(p)
    \/ \E p \in 1..N, m \in Messages: Receive1(p, m) \/ Receive2(p, m)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in 1..N, m \in Messages: Receive1(p, m))
        /\ WF_vars(\E p \in 1..N, m \in Messages: Receive2(p, m))
        /\ WF_vars(\E p \in 1..N: ComputeEstimate(p))
        /\ WF_vars(\E p \in 1..N: Decide(p))
        /\ WF_vars(\E p \in 1..N: Choose(p))

Validity == \A p \in 1..N: decided[p] # Bottom => \E q \in 1..N: decided[p] = prop[q]
Agreement == \A p, q \in 1..N: (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

Termination == <>(\A p \in 1..N: phase[p] \in {"done", "crashed"})
ConditionalTerm ==
    /\ (\E g \in 1..N: prop[g] = MaxIn(1..N, prop))
    /\ ([](\E g \in 1..N: prop[g] = MaxIn(1..N, prop)) ~> Termination)

====