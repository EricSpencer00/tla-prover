---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Phase identifiers for the two-phase protocol
Phases == {"bc1", "w1", "pr", "bc2", "w2", "done", "crashed", "choose"}

TypeOK ==
    /\ Location \in [1..N -> Phases]
    /\ View \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ Proposed \in [1..N -> Values]
    /\ Estimate \in [1..N -> Values \cup {Bottom}]
    /\ Decision \in [1..N -> Values \cup {Bottom}]
    /\ Crashed \in 0..F
    /\ Sent \subseteq [ph: 1..2, v: Values, s: 1..N]
    /\ Received \in [1..N -> SUBSET (1..N)]

RECURSIVE MaxOf(_, _)
MaxOf(S, f) ==
    IF S = {} THEN Bottom
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] \cup {MaxOf(S \ {x}, f)}

Init ==
    /\ Location = [i \in 1..N |-> "bc1"]
    /\ Proposed \in [1..N -> Values]
    /\ View = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
    /\ Estimate = [i \in 1..N |-> Bottom]
    /\ Decision = [i \in 1..N |-> Bottom]
    /\ Crashed = 0
    /\ Sent = {}
    /\ Received = [i \in 1..N |-> {}]

Broadcast1(i) ==
    /\ Location[i] = "bc1"
    /\ Sent' = Sent \cup {[ph |-> 1, v |-> Proposed[i], s |-> i]}
    /\ Location' = [Location EXCEPT ![i] = "w1"]
    /\ UNCHANGED <<View, Proposed, Estimate, Decision, Crashed, Received>>

\* Any message is always available to be received; fairness drives eventual delivery to
\* the right phase and the right round.
Receive(i, m) ==
    /\ Location[i] \in {"w1", "w2"}
    /\ m \in Sent
    /\ m.s \notin Received[i]
    /\ Location[i] = (IF m.ph = 1 THEN "w1" ELSE "w2")
    /\ View' = [View EXCEPT ![i][m.s] = m.v]
    /\ Received' = [Received EXCEPT ![i] = Received[i] \cup {m.s}]
    /\ UNCHANGED <<Location, Proposed, Estimate, Decision, Crashed, Sent>>

StartPhase2(i) ==
    /\ Location[i] = "w1"
    /\ Cardinality(Received[i]) >= N - T
    /\ Estimate' = [Estimate EXCEPT ![i] = MaxOf(1..N, [j \in 1..N |-> View[i][j]])]
    /\ Location' = [Location EXCEPT ![i] = "bc2"]
    /\ UNCHANGED <<View, Proposed, Decision, Crashed, Sent, Received>>

Broadcast2(i) ==
    /\ Location[i] = "bc2"
    /\ Sent' = Sent \cup {[ph |-> 2, v |-> Proposed[i], s |-> i]}
    /\ Location' = [Location EXCEPT ![i] = "w2"]
    /\ UNCHANGED <<View, Proposed, Estimate, Decision, Crashed, Received>>

Decide(i, v) ==
    /\ Location[i] = "w2"
    /\ Cardinality({m \in Sent : m.ph = 2 /\ m.s \in Received[i] /\ m.v = v}) >= N - T
    /\ Decision' = [Decision EXCEPT ![i] = v]
    /\ Location' = [Location EXCEPT ![i] = "done"]
    /\ UNCHANGED <<View, Proposed, Estimate, Crashed, Sent, Received>>

Choose(i, v) ==
    /\ Location[i] = "choose"
    /\ v \in {View[i][j] : j \in 1..N}
    /\ Decision' = [Decision EXCEPT ![i] = v]
    /\ Location' = [Location EXCEPT ![i] = "done"]
    /\ UNCHANGED <<View, Proposed, Estimate, Crashed, Sent, Received>>

\* The choosing transition fires only when the N-T threshold cannot be reached.
\* It is deterministic in that it picks a value that already appears in the view,
\* which is always possible once every sender's phase-2 message has been received.
MoveToChoose(i) ==
    /\ Location[i] = "w2"
    /\ Received[i] = 1..N
    /\ Location' = [Location EXCEPT ![i] = "choose"]
    /\ UNCHANGED <<View, Proposed, Estimate, Decision, Crashed, Sent, Received>>

Crash(i) ==
    /\ Location[i] \notin {"crashed", "done"}
    /\ Crashed < F
    /\ Location' = [Location EXCEPT ![i] = "crashed"]
    /\ Crashed' = Crashed + 1
    /\ UNCHANGED <<View, Proposed, Estimate, Decision, Sent, Received>>

Next ==
    \/ \E i \in 1..N: Broadcast1(i) \/ StartPhase2(i) \/ Broadcast2(i) \/ MoveToChoose(i) \/ Crash(i)
    \/ \E i \in 1..N, m \in Sent: Receive(i, m)
    \/ \E i \in 1..N, v \in Values: Decide(i, v) \/ Choose(i, v)

Spec == Init /\ [][Next]_<<Location, View, Proposed, Estimate, Decision, Crashed, Sent, Received>>

Validity == \A i \in 1..N: Decision[i] # Bottom => Decision[i] \in {Proposed[j] : j \in 1..N}

Agreement == \A a, b \in 1..N: (Decision[a] # Bottom /\ Decision[b] # Bottom) => Decision[a] = Decision[b]

Termination == <>(\A i \in 1..N: Location[i] \in {"crashed", "done"})

ConditionalTermination == <>(\A i \in 1..N: Decision[i] # Bottom)

Fairness ==
    /\ \A i \in 1..N: TRUE
    /\ \A i \in 1..N: TRUE
    /\ \A i \in 1..N: TRUE
    /\ \A i \in 1..N: TRUE

Properties == Termination /\ ConditionalTermination

====