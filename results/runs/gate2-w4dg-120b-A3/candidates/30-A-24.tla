---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Message types, phase-1 versus phase-2
MessageTypes == {"phase1", "phase2"}

\* Every sent message records its type, value, and sender; phase-2 messages
\* also record the sender's estimated value.
Message == [typ: MessageTypes, val: Values \cup {Bottom},
            sender: 0 .. (N - 1), est: Values \cup {Bottom}]

\* A process's local view of every other process's value is an N-by-N matrix.
Views == [0 .. (N - 1) -> [0 .. (N - 1) -> Values \cup {Bottom}]]

\* A process name is the string showing the phase it is currently in.
Locations == {"broadcast1", "waiting1", "prepare", "broadcast2",
              "waiting2", "done", "crashed", "choosing"}

VARIABLES loc, view, proposal, estimate, decision, crashed, sent, recv

vars == <<loc, view, proposal, estimate, decision,
           crashed, sent, recv>>

TypeOK ==
    /\ loc \in [0 .. (N - 1) -> Locations]
    /\ view \in Views
    /\ proposal \in [0 .. (N - 1) -> Values \cup {Bottom}]
    /\ estimate \in [0 .. (N - 1) -> Values \cup {Bottom}]
    /\ decision \in [0 .. (N - 1) -> Values \cup {Bottom}]
    /\ crashed \in 0 .. N
    /\ sent \subseteq Message
    /\ recv \subseteq Message

\* The maximum value a process has observed in its local view.
MaxInView(p) ==
    LET f[S \in SUBSET (Values \cup {Bottom})] ==
        IF S = {} THEN Bottom
        ELSE IF \E x \in S : \A y \in S : x >= y THEN CHOOSE x \in S : \A y \in S : x >= y
        ELSE Bottom
    IN f({view[p][q] : q \in 0 .. (N - 1)})

Init ==
    /\ loc = [p \in 0 .. (N - 1) |-> "broadcast1"]
    /\ view = [p \in 0 .. (N - 1) |-> [q \in 0 .. (N - 1) |-> Bottom]]
    /\ proposal \in [0 .. (N - 1) -> Values]
    /\ estimate = [p \in 0 .. (N - 1) |-> Bottom]
    /\ decision = [p \in 0 .. (N - 1) |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ recv = {}

\* A phase-1 broadcast is one message per process; the sender only moves on
\* once it has actually broadcast, so nothing is lost.
Broadcast1(p) ==
    /\ loc[p] = "broadcast1"
    /\ sent' = sent \cup {[typ |-> "phase1", val |-> proposal[p],
                           sender |-> p, est |-> Bottom]}
    /\ loc' = [loc EXCEPT ![p] = "waiting1"]
    /\ UNCHANGED <<view, proposal, estimate, decision, crashed, recv>>

\* A process may receive a phase-1 (or phase-2) message and updates its
\* local view if the message type matches the phase it is currently in.
Receive(p, m) ==
    /\ m \in sent
    /\ m \notin recv
    /\ m.sender # p
    /\ loc[p] \in {"waiting1", "waiting2"}
    /\ m.typ = (IF loc[p] = "waiting1" THEN "phase1" ELSE "phase2")
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ recv' = recv \cup {m}
    /\ UNCHANGED <<loc, proposal, estimate, decision, crashed, sent>>

\* Phase-1 waiting: once enough distinct phase-1 messages have arrived the
\* process computes its estimate and moves to the next phase.
Prepare(p) ==
    /\ loc[p] = "waiting1"
    /\ Cardinality({m \in recv : m.sender # p /\ m.typ = "phase1"}) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = MaxInView(p)]
    /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
    /\ UNCHANGED <<view, proposal, decision, crashed, sent, recv>>

\* Phase-2: the broadcast carries both the proposed value and the estimate.
Broadcast2(p) ==
    /\ loc[p] = "broadcast2"
    /\ sent' = sent \cup {[typ |-> "phase2", val |-> proposal[p],
                           sender |-> p, est |-> estimate[p]]}
    /\ loc' = [loc EXCEPT ![p] = "waiting2"]
    /\ UNCHANGED <<view, proposal, estimate, decision, crashed, recv>>

\* Phase-2 waiting: the quorum rule here applies to the estimated value,
\* which is the twist that makes the max-voting twist correct.
Decide(p) ==
    /\ loc[p] = "waiting2"
    /\ \E v \in Values :
        /\ Cardinality({m \in recv : m.sender # p /\ m.typ = "phase2" /\ m.est = v})
           >= N - T
        /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, proposal, estimate, crashed, sent, recv>>

\* When no single estimated value reaches the quorum, the process chooses.
Choose(p) ==
    /\ loc[p] = "waiting2"
    /\ Cardinality({m \in recv : m.sender # p /\ m.typ = "phase2"}) = N
    /\ \A v \in Values : Cardinality({m \in recv : m.sender # p /\ m.typ = "phase2" /\ m.est = v})
                       < N - T
    /\ loc' = [loc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, proposal, estimate, decision, crashed, sent, recv>>

DecideDeterministic(p) ==
    /\ loc[p] = "choosing"
    /\ \E v \in Values :
        /\ v \in {view[p][q] : q \in 0 .. (N - 1)}
        /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, proposal, estimate, crashed, sent, recv>>

Crash(p) ==
    /\ loc[p] \notin {"crashed", "done"}
    /\ crashed < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, proposal, estimate, decision, sent, recv>>

Next ==
    \/ \E p \in 0 .. (N - 1) : Broadcast1(p)
    \/ \E p \in 0 .. (N - 1) : \E m \in Message : Receive(p, m)
    \/ \E p \in 0 .. (N - 1) : Prepare(p)
    \/ \E p \in 0 .. (N - 1) : Broadcast2(p)
    \/ \E p \in 0 .. (N - 1) : Decide(p)
    \/ \E p \in 0 .. (N - 1) : Choose(p)
    \/ \E p \in 0 .. (N - 1) : DecideDeterministic(p)
    \/ \E p \in 0 .. (N - 1) : Crash(p)

Fairness ==
    /\ \A p \in 0 .. (N - 1) : WF_vars(\E m \in Message : Receive(p, m))
    /\ \A p \in 0 .. (N - 1) : WF_vars(Broadcast1(p))
    /\ \A p \in 0 .. (N - 1) : WF_vars(Prepare(p))
    /\ \A p \in 0 .. (N - 1) : WF_vars(Broadcast2(p))
    /\ \A p \in 0 .. (N - 1) : WF_vars(Decide(p))
    /\ \A p \in 0 .. (N - 1) : WF_vars(Choose(p))
    /\ \A p \in 0 .. (N - 1) : WF_vars(DecideDeterministic(p))

Spec == Init /\ [][Next]_vars /\ Fairness

Validity == \A p \in 0 .. (N - 1) : decision[p] # Bottom => decision[p] \in Values

Agreement == \A p, q \in 0 .. (N - 1) : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination == <>(\A p \in 0 .. (N - 1) : loc[p] \in {"done", "crashed"})

\* Condition C1: enough processes propose the maximum value to guarantee
\* termination under the twist.
ConditionC1 ==
    \E v \in Values :
        /\ v = (CHOOSE x \in Values : \A y \in Values : y <= x)
        /\ Cardinality({p \in 0 .. (N - 1) : proposal[p] = v}) >= F + 1

ConditionalTermination == ConditionC1 => Termination

Properties == Termination /\ ConditionalTermination

\* Model bounds: the reference configuration carries them as a comment rather
\* than an operator, so they are omitted here (the constants are still bound
\* by the CONSTANTS clause).
====