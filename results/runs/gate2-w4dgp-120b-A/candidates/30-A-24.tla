---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES phase, view, propose, estimate, decided, crashed, sent, received
vars == <<phase, view, propose, estimate, decided, crashed, sent, received>>

TypeOK ==
    /\ phase \in [1..N -> {"ph1_bcst", "ph1_wait", "preparing", "ph2_bcst", "ph2_wait", "done", "crashed", "choosing"}]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ propose \in [1..N -> Values]
    /\ estimate \in [1..N -> Values \cup {Bottom}]
    /\ decided \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..F
    /\ sent \subseteq [type: {"ph1", "ph2"}, val: Values \cup {Bottom}, est: Values \cup {Bottom}, from: 1..N]
    /\ received \in [1..N -> SUBSET [type: {"ph1", "ph2"}, val: Values \cup {Bottom}, est: Values \cup {Bottom}, from: 1..N]]

MaxOf(f) == LET g[S \in SUBSET Values] ==
                 IF S = {} THEN Bottom
                 ELSE LET x == CHOOSE y \in S : \A z \in S : y >= z IN x
             IN g[f]

Init ==
    /\ phase = [p \in 1..N |-> "ph1_bcst"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ propose \in [1..N -> Values]
    /\ estimate = [p \in 1..N |-> Bottom]
    /\ decided = [p \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ received = [p \in 1..N |-> {}]

Ph1Broadcast(p) ==
    /\ phase[p] = "ph1_bcst"
    /\ sent' = sent \cup {[type |-> "ph1", val |-> propose[p], est |-> Bottom, from |-> p]}
    /\ phase' = [phase EXCEPT ![p] = "ph1_wait"]
    /\ UNCHANGED <<view, propose, estimate, decided, crashed, received>>

Ph1Receive(p, m) ==
    /\ phase[p] = "ph1_wait"
    /\ m.type = "ph1"
    /\ m.from \notin {q.from : q \in received[p]}
    /\ view' = [view EXCEPT ![p][m.from] = m.val]
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ UNCHANGED <<phase, propose, estimate, decided, crashed, sent>>

Ph1Proceed(p) ==
    /\ phase[p] = "ph1_wait"
    /\ Cardinality({m.from : m \in received[p] : m.type = "ph1"}) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = MaxOf(view[p])]
    /\ phase' = [phase EXCEPT ![p] = "ph2_bcst"]
    /\ UNCHANGED <<view, propose, decided, crashed, sent, received>>

Ph2Broadcast(p) ==
    /\ phase[p] = "ph2_bcst"
    /\ sent' = sent \cup {[type |-> "ph2", val |-> propose[p], est |-> estimate[p], from |-> p]}
    /\ phase' = [phase EXCEPT ![p] = "ph2_wait"]
    /\ UNCHANGED <<view, propose, estimate, decided, crashed, received>>

Ph2Decide(p, m) ==
    /\ phase[p] = "ph2_wait"
    /\ m.type = "ph2"
    /\ m.from \notin {q.from : q \in received[p]}
    /\ Cardinality({q \in received[p] \cup {m} : q.type = "ph2" /\ q.est = m.est}) >= N - T
    /\ decided' = [decided EXCEPT ![p] = m.est]
    /\ phase' = [phase EXCEPT ![p] = "done"]
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ UNCHANGED <<view, propose, estimate, crashed, sent>>

Ph2Choose(p, m) ==
    /\ phase[p] = "ph2_wait"
    /\ m.type = "ph2"
    /\ m.from \notin {q.from : q \in received[p]}
    /\ Cardinality({q.from : q \in received[p] \cup {m} : q.type = "ph2"}) = N
    /\ phase' = [phase EXCEPT ![p] = "choosing"]
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ UNCHANGED <<view, propose, estimate, decided, crashed, sent>>

Choose(p) ==
    /\ phase[p] = "choosing"
    /\ \E v \in Values : v \in {view[p][q] : q \in 1..N} /\ decided' = [decided EXCEPT ![p] = v]
    /\ phase' = [phase EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, propose, estimate, crashed, sent, received>>

Crash(p) ==
    /\ crashed < F
    /\ phase[p] \notin {"done", "crashed"}
    /\ crashed' = crashed + 1
    /\ phase' = [phase EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<view, propose, estimate, decided, sent, received>>

Next ==
    \/ \E p \in 1..N : Ph1Broadcast(p) \/ Ph1Proceed(p) \/ Ph2Broadcast(p) \/ Choose(p) \/ Crash(p)
    \/ \E p \in 1..N, m \in [type: {"ph1", "ph2"}, val: Values \cup {Bottom}, est: Values \cup {Bottom}, from: 1..N] :
         Ph1Receive(p, m) \/ Ph2Decide(p, m) \/ Ph2Choose(p, m)

Spec ==
    /\ Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E p \in 1..N, m \in [type: {"ph1", "ph2"}, val: Values \cup {Bottom}, est: Values \cup {Bottom}, from: 1..N] : Ph1Receive(p, m))
    /\ WF_vars(\E p \in 1..N : Ph1Proceed(p))
    /\ WF_vars(\E p \in 1..N, m \in [type: {"ph1", "ph2"}, val: Values \cup {Bottom}, est: Values \cup {Bottom}, from: 1..N] : Ph2Decide(p, m))
    /\ WF_vars(\E p \in 1..N, m \in [type: {"ph1", "ph2"}, val: Values \cup {Bottom}, est: Values \cup {Bottom}, from: 1..N] : Ph2Choose(p, m))
    /\ WF_vars(\E p \in 1..N : Choose(p))

Validity == \A p \in 1..N : decided[p] # Bottom => \E q \in 1..N : propose[q] = decided[p]

Agreement == \A p, q \in 1..N : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

Termination == \A p \in 1..N : <>(phase[p] \in {"done", "crashed"})

ConditionC1 == \A p \in 1..N :
    (\A q \in 1..N : propose[q] = MaxOf(propose) => propose[p] = MaxOf(propose))
    => (phase[p] = "ph1_bcst" \/ phase[p] = "crashed")

RECURSIVE MaxOfF(_)
MaxOfF(S) == IF S = {} THEN Bottom ELSE LET x == CHOOSE y \in S : \A z \in S : y >= z IN x

ConditionC1Term == \A p \in 1..N : (\A q \in 1..N : propose[q] = MaxOfF(propose) => propose[p] = MaxOfF(propose)) => (phase[p] = "ph1_bcst" \/ phase[p] = "crashed")

WfCoherence ==
    /\ 2 * T < N
    /\ 0 <= F /\ F <= T
    /\ \A v \in Values : v # Bottom

====