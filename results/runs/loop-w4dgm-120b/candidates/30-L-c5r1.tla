---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Phases == {"b1", "w1", "prep", "b2", "w2", "done", "crashed", "choosing"}
MsgTypes == {"p1", "p2"}
\* A message carries its type, the sender's proposed value, and (for phase 2)
\* the sender's estimated value.
Msgs == MsgTypes \X Values \X (0 .. (N - 1))

VARIABLES loc, known, propose, estimate, decided, crashed, sent, recvd

vars == <<loc, known, propose, estimate, decided, crashed, sent, recvd>>

TypeOK ==
    /\ loc \in [0 .. (N - 1) -> Phases]
    /\ known \in [0 .. (N - 1) -> [0 .. (N - 1) -> Values \cup {Bottom}]]
    /\ propose \in [0 .. (N - 1) -> Values]
    /\ estimate \in [0 .. (N - 1) -> Values \cup {Bottom}]
    /\ decided \in [0 .. (N - 1) -> Values \cup {Bottom}]
    /\ crashed \in 0 .. N
    /\ sent \subseteq Msgs
    /\ recvd \in [0 .. (N - 1) -> SUBSET Msgs]

\* A value is in a process's local view once some received message carries it.
InView(p, v) == \E m \in recvd[p] : v = m[2]

Init ==
    /\ loc = [p \in 0 .. (N - 1) |-> "b1"]
    /\ known = [p \in 0 .. (N - 1) |-> [q \in 0 .. (N - 1) |-> Bottom]]
    /\ propose \in [0 .. (N - 1) -> Values]
    /\ estimate = [p \in 0 .. (N - 1) |-> Bottom]
    /\ decided = [p \in 0 .. (N - 1) |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ recvd = [p \in 0 .. (N - 1) |-> {}]

\* Phase-1 broadcast: the first phase always runs, regardless of the condition.
BroadcastP1(p) ==
    /\ loc[p] = "b1"
    /\ sent' = sent \cup {<<"p1", propose[p], p>>}
    /\ loc' = [loc EXCEPT ![p] = "w1"]
    /\ UNCHANGED <<known, propose, estimate, decided, crashed, recvd>>

ReceiveP1(p, m) ==
    /\ loc[p] = "w1"
    /\ m \in recvd[p]
    /\ m[1] = "p1"
    /\ known' = [known EXCEPT ![p][m[3]] = m[2]]
    /\ UNCHANGED <<loc, propose, estimate, decided, crashed, sent, recvd>>

\* Phase 1 finishes only once enough distinct messages survive the asynchrony.
Prepare(p) ==
    /\ loc[p] = "w1"
    /\ Cardinality({m \in recvd[p] : m[1] = "p1"}) >= (N - T)
    /\ estimate' = [estimate EXCEPT ![p] = Max({known[p][q] : q \in 0 .. (N - 1)} \cup {propose[p]})]
    /\ loc' = [loc EXCEPT ![p] = "b2"]
    /\ UNCHANGED <<known, propose, decided, crashed, sent, recvd>>

BroadcastP2(p) ==
    /\ loc[p] = "b2"
    /\ sent' = sent \cup {<<"p2", propose[p], estimate[p], p>>}
    /\ loc' = [loc EXCEPT ![p] = "w2"]
    /\ UNCHANGED <<known, propose, estimate, decided, crashed, recvd>>

ReceiveP2(p, m) ==
    /\ loc[p] = "w2"
    /\ m \in recvd[p]
    /\ m[1] = "p2"
    /\ known' = [known EXCEPT ![p][m[3]] = m[2]]
    /\ UNCHANGED <<loc, propose, estimate, decided, crashed, sent, recvd>>

Decide(p) ==
    /\ loc[p] = "w2"
    /\ \E v \in Values :
        /\ Cardinality({m \in recvd[p] : m[1] = "p2" /\ m[4] = v}) >= (N - T)
        /\ decided' = [decided EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<known, propose, estimate, crashed, sent, recvd>>

\* Deterministic tie-breaking if every sender is seen but no estimate reaches
\* the Crash Fault Tolerance threshold.
Choose(p) ==
    /\ loc[p] = "w2"
    /\ \A q \in 0 .. (N - 1) : \E m \in recvd[p] : m[3] = q
    /\ \A v \in Values : Cardinality({m \in recvd[p] : m[1] = "p2" /\ m[4] = v}) < (N - T)
    /\ \E v \in Values : InView(p, v) /\ decided' = [decided EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<known, propose, estimate, crashed, sent, recvd>>

Crash(p) ==
    /\ crashed < F
    /\ loc[p] \notin {"done", "crashed"}
    /\ crashed' = crashed + 1
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<known, propose, estimate, decided, sent, recvd>>

ReceiveAny(p) == \E m \in Msgs : ReceiveP1(p, m) \/ ReceiveP2(p, m)

Next ==
    \/ \E p \in 0 .. (N - 1) : BroadcastP1(p) \/ Prepare(p) \/ BroadcastP2(p) \/ Decide(p) \/ Choose(p) \/ Crash(p)
    \/ \E p \in 0 .. (N - 1), m \in Msgs : ReceiveP1(p, m) \/ ReceiveP2(p, m)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in 0 .. (N - 1) : WF_vars(ReceiveAny(p))

\* A decided value must have been proposed by somebody.
Validity ==
    \A p \in 0 .. (N - 1) : decided[p] # Bottom => (\E q \in 0 .. (N - 1) : propose[q] = decided[p])

Agreement ==
    \A p, q \in 0 .. (N - 1) : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

Termination == <>(\A p \in 0 .. (N - 1) : loc[p] \in {"done", "crashed"})

\* Condition C1: the guaranteed-termination condition from the paper.
C1Terminates == (\A q \in 0 .. (N - 1) : propose[q] = Max(Values)) => Termination

====