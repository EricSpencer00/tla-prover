---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ 2 * T < N
       /\ F \in 0 .. T
       /\ N > 0
       /\ Bottom \notin Values

\* A value is the pair of its numeric rank and the concrete value drawn from the
\* set, so MaxV really is a numeric maximum that incomparable Values would still
\* let us compute correctly.
ValuePairs == Values \X (1 .. Cardinality(Values))
MaxV == CHOOSE v \in ValuePairs : \A w \in ValuePairs : v[2] >= w[2]

VARIABLES loc, view, proposed, estimate, decided, crashed, sent, recvd

Vars == <<loc, view, proposed, estimate, decided, crashed, sent, recvd>>

Locs == [N -> {"b1", "w1", "p2", "b2", "w2", "done", "crash", "choose"}]
Msgs == [type : {"p1", "p2"}, val : ValuePairs, sender : 1 .. N, ev : ValuePairs]

TypeOK ==
  /\ loc \in Locs
  /\ view \in [1 .. N -> [1 .. N -> ValuePairs \cup {Bottom}]]
  /\ proposed \in [1 .. N -> ValuePairs]
  /\ estimate \in [1 .. N -> ValuePairs]
  /\ decided \in [1 .. N -> ValuePairs \cup {Bottom}]
  /\ crashed \in 0 .. N
  /\ sent \subseteq Msgs
  /\ recvd \in [1 .. N -> SUBSET Msgs]

Init ==
  /\ loc = [i \in 1 .. N |-> "b1"]
  /\ view = [i \in 1 .. N |-> [j \in 1 .. N |-> Bottom]]
  /\ proposed = [i \in 1 .. N |-> CHOOSE v \in ValuePairs : TRUE]
  /\ estimate = [i \in 1 .. N |-> MaxV]
  /\ decided = [i \in 1 .. N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recvd = [i \in 1 .. N |-> {}]

Broadcast1(i) ==
  /\ loc[i] = "b1"
  /\ sent' = sent \cup {[type |-> "p1", val |-> proposed[i], sender |-> i, ev |-> MaxV]}
  /\ loc' = [loc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashed, recvd>>

Deliver1(i, m) ==
  /\ loc[i] \in {"w1", "p2"}
  /\ m \in recvd[i]
  /\ m.type = "p1"
  /\ view[i][m.sender] = Bottom
  /\ view' = [view EXCEPT ![i][m.sender] = m.val]
  /\ UNCHANGED <<loc, proposed, estimate, decided, crashed, sent, recvd>>

\* A process computes its estimate from its local view; the view may still be
\* incomplete, which is what makes the two-phase guesswork different from voting.
Estimate(i) ==
  /\ loc[i] = "w1"
  /\ Cardinality({j \in 1 .. N : view[i][j] # Bottom}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = MaxV]
  /\ loc' = [loc EXCEPT ![i] = "p2"]
  /\ UNCHANGED <<view, proposed, decided, crashed, sent, recvd>>

Broadcast2(i) ==
  /\ loc[i] = "p2"
  /\ sent' = sent \cup {[type |-> "p2", val |-> proposed[i], sender |-> i, ev |-> estimate[i]]}
  /\ loc' = [loc EXCEPT ![i] = "w2"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashed, recvd>>

\* The threshold is on the number of matching estimated values, not on who sent
\* them, so a slow-but-not-crashed process can always keep catching up.
DecideOnMajority(i) ==
  /\ loc[i] = "w2"
  /\ Cardinality({m \in recvd[i] : m.type = "p2" /\ m.ev = estimate[i]}) >= N - T
  /\ decided' = [decided EXCEPT ![i] = estimate[i]]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, recvd>>

\* A process that cannot reach the threshold picks any observed value instead.
Choose(i) ==
  /\ loc[i] = "w2"
  /\ Cardinality({m \in recvd[i] : m.type = "p2"}) = N
  /\ \A v \in Values : Cardinality({m \in recvd[i] : m.type = "p2" /\ m.ev = v}) < N - T
  /\ loc' = [loc EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashed, sent, recvd>>

PickObserved(i) ==
  /\ loc[i] = "choose"
  /\ \E v \in Values : decided' = [decided EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, recvd>>

Idle(i) ==
  /\ loc[i] \in {"done", "crash"}
  /\ UNCHANGED Vars

Crash(i) ==
  /\ loc[i] \notin {"done", "crash"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crash"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposed, estimate, decided, sent, recvd>>

\* The network is finite, so each process's receive set can be modeled as a set
\* that eventually fills up.
Receive1(i) == \E m \in Msgs : Deliver1(i, m)
Receive2(i) == \E m \in Msgs : Deliver1(i, m)

Next ==
  \/ \E i \in 1 .. N : Broadcast1(i) \/ Estimate(i) \/ Broadcast2(i)
                     \/ DecideOnMajority(i) \/ Choose(i) \/ Idle(i) \/ Crash(i)
  \/ \E i \in 1 .. N, m \in Msgs : Deliver1(i, m)
  \/ \E i \in 1 .. N : Receive1(i)
  \/ \E i \in 1 .. N : Receive2(i)

Spec == Init /\ [][Next]_Vars
        /\ WF_Vars(\E i \in 1 .. N : Receive1(i))
        /\ WF_Vars(\E i \in 1 .. N : Receive2(i))
        /\ WF_Vars(\E i \in 1 .. N : Estimate(i))
        /\ WF_Vars(\E i \in 1 .. N : DecideOnMajority(i))
        /\ WF_Vars(\E i \in 1 .. N : Choose(i))

\* Safety: a decision never comes out of thin air.
Validity == \A i \in 1 .. N : decided[i] # Bottom => decided[i] \in Values

Agreement == \A i, j \in 1 .. N :
  (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Termination == <>(crashed = N \/ \A i \in 1 .. N : loc[i] = "done")

\* The strong condition that guarantees the above without it:
ConditionC1 == Cardinality({i \in 1 .. N : proposed[i] = MaxV}) >= F + 1

ConditionalTermination == ConditionC1 ~> (<>(\A i \in 1 .. N : loc[i] = "done"))

====