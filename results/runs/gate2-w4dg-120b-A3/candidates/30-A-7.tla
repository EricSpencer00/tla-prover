---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* A message carries an id, type, value, and for phase 2 an estimated value.
Message == [id : 1..N, kind : {"phase1", "phase2"}, val : Values,
            est : Values \cup {Bottom}]

VARIABLES pc, view, prop, estimate, decision, crashed, sent, inbox

vars == <<pc, view, prop, estimate, decision, crashed, sent, inbox>>

Locs == {"broadcast1", "wait1", "prepare", "broadcast2", "wait2",
         "done", "crashed", "choosing"}

RECURSIVE MaxOf(_, _)
MaxOf(f, S) ==
    IF S = {} THEN Bottom
    ELSE LET x == CHOOSE y \in S : TRUE IN
         LET rest == S \ {x} IN
         LET m == MaxOf(f, rest) IN
         IF f[x] = Bottom THEN m
         ELSE IF m = Bottom THEN f[x]
         ELSE IF f[x] > m THEN f[x]
         ELSE m

TypeOK ==
    /\ pc \in [0..(N-1) -> Locs]
    /\ view \in [0..(N-1) -> [0..(N-1) -> Values \cup {Bottom}]]
    /\ prop \in [0..(N-1) -> Values]
    /\ estimate \in [0..(N-1) -> Values \cup {Bottom}]
    /\ decision \in [0..(N-1) -> Values \cup {Bottom}]
    /\ crashed \in 0..F
    /\ sent \subseteq Message
    /\ inbox \in [0..(N-1) -> SUBSET Message]

\* Each process proposes some value from the value set.
Init ==
    /\ pc = [p \in 0..(N-1) |-> "broadcast1"]
    /\ view = [p \in 0..(N-1) |-> [q \in 0..(N-1) |-> Bottom]]
    /\ prop \in [0..(N-1) -> Values]
    /\ estimate = [p \in 0..(N-1) |-> Bottom]
    /\ decision = [p \in 0..(N-1) |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ inbox = [p \in 0..(N-1) |-> {}]

\* Phase 1: broadcast the proposed value.
BroadcastPhase1(p) ==
    /\ pc[p] = "broadcast1"
    /\ sent' = sent \cup {[id |-> p, kind |-> "phase1", val |-> prop[p], est |-> Bottom]}
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashed, inbox>>

\* A process incorporates a message into its local view.
Receive(p, m) ==
    /\ pc[p] \in {"wait1", "wait2"}
    /\ m \in sent
    /\ m \notin inbox[p]
    /\ m.kind = (IF pc[p] = "wait1" THEN "phase1" ELSE "phase2")
    /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \cup {m}]
    /\ view' = [view EXCEPT ![p][m.id] = m.val]
    /\ UNCHANGED <<pc, prop, estimate, decision, crashed, sent>>

\* Once enough phase-1 messages are collected, compute the estimate and move on.
Prepare(p) ==
    /\ pc[p] = "wait1"
    /\ Cardinality({m.id \in inbox[p] : m.kind = "phase1"}) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = MaxOf(view, 0..(N-1))]
    /\ pc' = [pc EXCEPT ![p] = "broadcast2"]
    /\ UNCHANGED <<view, prop, decision, crashed, sent, inbox>>

\* Phase 2: broadcast both the proposal and the computed estimate.
BroadcastPhase2(p) ==
    /\ pc[p] = "broadcast2"
    /\ sent' = sent \cup {[id |-> p, kind |-> "phase2", val |-> prop[p],
                          est |-> estimate[p]]}
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashed, inbox>>

\* If enough phase-2 messages agree on an estimate, decide it.
Decide(p) ==
    /\ pc[p] = "wait2"
    /\ \E v \in Values :
         /\ Cardinality({m \in inbox[p] :
                          m.kind = "phase2" /\ m.est = v}) >= N - T
         /\ decision' = [decision EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashed, sent, inbox>>

\* If the threshold was missed, choose some value from the view.
Choose(p) ==
    /\ pc[p] = "wait2"
    /\ \A v \in Values :
         Cardinality({m \in inbox[p] :
                       m.kind = "phase2" /\ m.est = v}) < N - T
    /\ decision' = [decision EXCEPT ![p] \in {view[p][q] : q \in 0..(N-1)}]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashed, sent, inbox>>

\* A process may crash, bounded by the fault tolerance.
Crash(p) ==
    /\ pc[p] \notin {"crashed", "done"}
    /\ crashed < F
    /\ crashed' = crashed + 1
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<view, prop, estimate, decision, sent, inbox>>

Next ==
    \/ \E p \in 0..(N-1) : BroadcastPhase1(p) \/ Prepare(p)
                          \/ BroadcastPhase2(p) \/ Decide(p) \/ Choose(p) \/ Crash(p)
    \/ \E p \in 0..(N-1), m \in Message : Receive(p, m)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in 0..(N-1) : BroadcastPhase1(p))
        /\ WF_vars(\E p \in 0..(N-1) : BroadcastPhase2(p))
        /\ WF_vars(\E p \in 0..(N-1) : Prepare(p))
        /\ WF_vars(\E p \in 0..(N-1) : Decide(p))
        /\ WF_vars(\E p \in 0..(N-1) : Choose(p))

\* Validity: a decided value was actually proposed.
Validity ==
    \A p \in 0..(N-1) : decision[p] # Bottom => \E q \in 0..(N-1) : prop[q] = decision[p]

\* Agreement: no two processes ever decide different values.
Agreement ==
    \A p, q \in 0..(N-1) :
        (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

\* The protocol terminates (or crashes out).
Terminating == <>(\A p \in 0..(N-1) : pc[p] \in {"done", "crashed"})

MaxProposed == \E p \in 0..(N-1) : prop[p] = MaxOf(prop, 0..(N-1))

\* Conditional termination: under condition C1 (enough max proposals) it terminates.
ConditionalTermination == MaxProposed ~> Terminating

\* The model must respect the fault-tolerance bound.
BoundedFaults == 2 * T < N

Properties == Terminating /\ ConditionalTermination /\ BoundedFaults

====