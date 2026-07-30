---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Phase-1 messages only carry the proposed value; phase-2 messages carry
\* both the proposed value and the estimator derived from the local view.
MessageTypes == {"p1", "p2"}
Messages == [type: MessageTypes, val: Values, sender: 0..(N-1), est: Values]

\* Control locations: the protocol proceeds through the two phases, then
\* either decides by majority on the estimate or deterministically chooses.
Locs == {"bcast1", "wait1", "prepare", "bcast2", "wait2", "done", "crashed", "choosing"}

VARIABLES loc, view, prop, estimate, decision, crashed, sent, received

vars == <<loc, view, prop, estimate, decision, crashed, sent, received>>

TypeOK ==
  /\ loc \in [0..(N-1) -> Locs]
  /\ view \in [0..(N-1), 0..(N-1) -> Values \cup {Bottom}]
  /\ prop \in [0..(N-1) -> Values]
  /\ estimate \in [0..(N-1) -> Values \cup {Bottom}]
  /\ decision \in [0..(N-1) -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sent \subseteq Messages
  /\ received \in [0..(N-1) -> SUBSET Messages]

Init ==
  /\ loc = [i \in 0..(N-1) |-> "bcast1"]
  /\ view = [i \in 0..(N-1), j \in 0..(N-1) |-> Bottom]
  /\ prop \in [0..(N-1) -> Values]
  /\ estimate = [i \in 0..(N-1) |-> Bottom]
  /\ decision = [i \in 0..(N-1) |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [i \in 0..(N-1) |-> {}]

Send(m) == sent' = sent \cup {m}
Recv(m, i) == received' = [received EXCEPT ![i] = @ \cup {m}]

Bcast1(i) ==
  /\ loc[i] = "bcast1"
  /\ Send([type |-> "p1", val |-> prop[i], sender |-> i, est |-> Bottom])
  /\ loc' = [loc EXCEPT ![i] = "wait1"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, received>>

\* Receiving is type-gated: messages from the wrong phase are dropped, which
\* is what keeps the two phases' data separate.
RecvMatch1(m, i) ==
  /\ loc[i] \in {"wait1", "prepare"}
  /\ m.type = "p1"
  /\ loc[m.sender] = "wait1"
  /\ view[i][m.sender] = Bottom
  /\ view' = [view EXCEPT ![i][m.sender] = m.val]
  /\ Recv(m, i)
  /\ UNCHANGED <<loc, prop, estimate, decision, crashed, sent>>

Phase1Ready(i) ==
  /\ loc[i] = "wait1"
  /\ Cardinality({j \in 0..(N-1) : view[i][j] # Bottom}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] =
        IF Cardinality({j \in 0..(N-1) : view[i][j] # Bottom}) = 0
        THEN Bottom
        ELSE CHOOSE x \in Values :
               \E S \in SUBSET {j \in 0..(N-1) : view[i][j] # Bottom} :
                 S # {} /\ \A j \in S : view[i][j] = x /\ \A y \in Values : y \in Values => (y > x => \A k \in S : y > view[i][k]))
    ]
  /\ loc' = [loc EXCEPT ![i] = "bcast2"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, received>>

Bcast2(i) ==
  /\ loc[i] = "bcast2"
  /\ Send([type |-> "p2", val |-> prop[i], sender |-> i, est |-> estimate[i]])
  /\ loc' = [loc EXCEPT ![i] = "wait2"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, sent, received>>

RecvMatch2(m, i) ==
  /\ loc[i] \in {"wait2", "choosing"}
  /\ m.type = "p2"
  /\ loc[m.sender] \in {"wait2", "choosing"}
  /\ view' = [view EXCEPT ![i][m.sender] = m.est]
  /\ Recv(m, i)
  /\ UNCHANGED <<loc, prop, estimate, decision, crashed, sent>>

DecideByMajority(i) ==
  /\ loc[i] = "wait2"
  /\ \E v \in Values :
       Cardinality({j \in 0..(N-1) : view[i][j] = v}) >= N - T
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, received>>

\* Deterministic tie-breaking: when no estimate reached the threshold,
\* the process picks any value it has seen in its view.
Choose(i) ==
  /\ loc[i] = "wait2"
  /\ \A v \in Values : Cardinality({j \in 0..(N-1) : view[i][j] = v}) < N - T
  /\ loc' = [loc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, sent, received>>

DeterministicPick(i) ==
  /\ loc[i] = "choosing"
  /\ \E v \in Values :
       Cardinality({j \in 0..(N-1) : view[i][j] = v}) >= 1
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, received>>

Crash(i) ==
  /\ loc[i] \notin {"crashed", "done"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, estimate, decision, sent, received>>

Next ==
  \/ \E i \in 0..(N-1) : Bcast1(i)
  \/ \E m \in sent, i \in 0..(N-1) : RecvMatch1(m, i)
  \/ \E i \in 0..(N-1) : Phase1Ready(i)
  \/ \E i \in 0..(N-1) : Bcast2(i)
  \/ \E m \in sent, i \in 0..(N-1) : RecvMatch2(m, i)
  \/ \E i \in 0..(N-1) : DecideByMajority(i)
  \/ \E i \in 0..(N-1) : Choose(i)
  \/ \E i \in 0..(N-1) : DeterministicPick(i)
  \/ \E i \in 0..(N-1) : Crash(i)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E m \in sent, i \in 0..(N-1) : RecvMatch1(m, i))
        /\ WF_vars(\E i \in 0..(N-1) : Phase1Ready(i))
        /\ WF_vars(\E m \in sent, i \in 0..(N-1) : RecvMatch2(m, i))
        /\ WF_vars(\E i \in 0..(N-1) : DecideByMajority(i))
        /\ WF_vars(\E i \in 0..(N-1) : Choose(i))
        /\ WF_vars(\E i \in 0..(N-1) : DeterministicPick(i))

Validity == \A i \in 0..(N-1) : decision[i] # Bottom => \E j \in 0..(N-1) : decision[i] = prop[j]

Agreement == \A i, k \in 0..(N-1) : decision[i] # Bottom /\ decision[k] # Bottom => decision[i] = decision[k]

Termination == <>(\A i \in 0..(N-1) : loc[i] \in {"crashed", "done"})

\* Condition C1: at least F+1 processes propose the maximum value.
CondC1 == \E v \in Values :
  (\A w \in Values : w > v => Cardinality({j \in 0..(N-1) : prop[j] = w}) = 0)
  /\ Cardinality({j \in 0..(N-1) : prop[j] = v}) >= F + 1

ConditionalTermination == CondC1 => Termination

====