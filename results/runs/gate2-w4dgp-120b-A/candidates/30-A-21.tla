---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, proposed, estimate, decided, crashed, sent, recvd
vars == <<loc, view, proposed, estimate, decided, crashed, sent, recvd>>

\* 2T < N is the condition on the number of tolerated faults; without it a
\* faulty majority cannot be distinguished from a crash. The "choose" state
\* implements the fallback: if the condition fails a process picks from its
\* own view instead of waiting for an N-T agreement.
RECURSIVE MaxOf(_, _)
MaxOf(S, f) ==
    IF S = {} THEN Bottom
    ELSE LET x == CHOOSE y \in S : TRUE
             m == MaxOf(S \ {x}, f)
         IN IF f[x] > m THEN f[x] ELSE m

TypeOK ==
    /\ loc \in [1..N -> {"bcast1", "wait1", "prep", "bcast2", "wait2", "done", "crashed", "choose"}]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ proposed \in [1..N -> Values]
    /\ estimate \in [1..N -> Values \cup {Bottom}]
    /\ decided \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..F
    /\ sent \subseteq [type: {"p1", "p2"}, val: Values, sender: 1..N, est: Values \cup {Bottom}]
    /\ recvd \in [1..N -> SUBSET [type: {"p1", "p2"}, val: Values, sender: 1..N, est: Values \cup {Bottom}]]

Init ==
    /\ loc = [p \in 1..N |-> "bcast1"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ proposed \in [1..N -> Values]
    /\ estimate = [p \in 1..N |-> Bottom]
    /\ decided = [p \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ recvd = [p \in 1..N |-> {}]

Broadcast1(p) ==
    /\ loc[p] = "bcast1"
    /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ sent' = sent \cup {[type |-> "p1", val |-> proposed[p], sender |-> p, est |-> Bottom]}
    /\ UNCHANGED <<view, proposed, estimate, decided, crashed, recvd>>

Receive1(p, m) ==
    /\ loc[p] = "wait1"
    /\ m \in sent
    /\ m.type = "p1"
    /\ view[p][m.sender] = Bottom
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ recvd' = [recvd EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED <<loc, proposed, estimate, decided, crashed, sent>>

Prepare(p) ==
    /\ loc[p] = "wait1"
    /\ Cardinality({x \in recvd[p] : x.type = "p1"}) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = MaxOf(1..N, view[p])]
    /\ loc' = [loc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED <<view, proposed, decided, crashed, sent, recvd>>

Broadcast2(p) ==
    /\ loc[p] = "bcast2"
    /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ sent' = sent \cup {[type |-> "p2", val |-> proposed[p], sender |-> p, est |-> estimate[p]]}
    /\ UNCHANGED <<view, proposed, estimate, decided, crashed, recvd>>

Decide2(p, v) ==
    /\ loc[p] = "wait2"
    /\ Cardinality({x \in recvd[p] : x.type = "p2" /\ x.est = v}) >= N - T
    /\ decided' = [decided EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, proposed, estimate, sent, recvd, crashed>>

Fallback(p) ==
    /\ loc[p] = "wait2"
    /\ \A q \in 1..N : [type |-> "p2", val |-> proposed[q], sender |-> q, est |-> estimate[q]] \in recvd[p]
    /\ loc' = [loc EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<view, proposed, estimate, decided, sent, recvd, crashed>>

Choose(p, v) ==
    /\ loc[p] = "choose"
    /\ \E q \in 1..N : view[p][q] = v
    /\ decided' = [decided EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, proposed, estimate, sent, recvd, crashed>>

Crash(p) ==
    /\ crashed < F
    /\ loc[p] \notin {"crashed", "done"}
    /\ crashed' = crashed + 1
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<view, proposed, estimate, decided, sent, recvd>>

Next ==
    \/ \E p \in 1..N : Broadcast1(p) \/ Prepare(p) \/ Broadcast2(p) \/ Fallback(p) \/ Crash(p)
    \/ \E p \in 1..N, m \in sent : Receive1(p, m)
    \/ \E p \in 1..N, v \in Values : Decide2(p, v) \/ Choose(p, v)
    \/ UNCHANGED vars

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in 1..N, m \in sent : Receive1(p, m))
    /\ WF_vars(\E p \in 1..N : Broadcast1(p))
    /\ WF_vars(\E p \in 1..N : Prepare(p))
    /\ WF_vars(\E p \in 1..N : Broadcast2(p))
    /\ WF_vars(\E p \in 1..N, v \in Values : Decide2(p, v))
    /\ WF_vars(\E p \in 1..N : Fallback(p))
    /\ WF_vars(\E p \in 1..N, v \in Values : Choose(p, v))
    /\ WF_vars(\E p \in 1..N : Crash(p))

\* Decision values never come out of thin air: they are always one of the
\* proposals that some process actually put forward.
Validity == \A p \in 1..N : decided[p] # Bottom => \E q \in 1..N : decided[p] = proposed[q]

Agreement == \A p, q \in 1..N : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

Terminate == <>(\A p \in 1..N : loc[p] \in {"done", "crashed"})

CondTerminate == <>(\A p \in 1..N : loc[p] \in {"done", "crashed"}) /\ Terminate

====