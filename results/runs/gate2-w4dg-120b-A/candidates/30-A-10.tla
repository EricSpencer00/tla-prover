---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ N > 0
       /\ 2 * T < N
       /\ 0 <= F /\ F <= T
       /\ Bottom \notin Values
       /\ \A a, b \in Values : a = b \/ a # b

Locations == {"ph1b", "ph1w", "prep", "ph2b", "ph2w", "done", "crashed", "choose"}

VARIABLES loc, view, prop, est, decision, crashed, sent, rcvd

vars == <<loc, view, prop, est, decision, crashed, sent, rcvd>>

Messages == [type : {"ph1", "ph2"}, val : Values, snd : 1..N, ev : Values \cup {Bottom}]

RECURSIVE MaxVals(_)
MaxVals(S) ==
  IF S = {} THEN Bottom
  ELSE LET x == CHOOSE y \in S : TRUE IN
       LET rest == MaxVals(S \ {x}) IN
         IF x # Bottom /\ (rest = Bottom \/ x > rest) THEN x ELSE rest

Init ==
  /\ loc = [p \in 1..N |-> "ph1b"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ prop \in [p \in 1..N |-> Values]
  /\ est = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ rcvd = [p \in 1..N |-> {}]

Phase1Send(p) ==
  /\ loc[p] = "ph1b"
  /\ sent' = sent \cup {[type |-> "ph1", val |-> prop[p], snd |-> p, ev |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "ph1w"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, rcvd>>

Phase1Recv(p, m) ==
  /\ loc[p] = "ph1w"
  /\ m.type = "ph1"
  /\ view[p][m.snd] = Bottom
  /\ view' = [view EXCEPT ![p][m.snd] = m.val]
  /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

ComputeEst(p) ==
  /\ loc[p] = "ph1w"
  /\ Cardinality({m \in rcvd[p] : m.type = "ph1"}) >= N - T
  /\ est' = [est EXCEPT ![p] = MaxVals({view[p][q] : q \in 1..N})]
  /\ loc' = [loc EXCEPT ![p] = "ph2b"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, rcvd>>

Phase2Send(p) ==
  /\ loc[p] = "ph2b"
  /\ sent' = sent \cup {[type |-> "ph2", val |-> prop[p], snd |-> p, ev |-> est[p]]}
  /\ loc' = [loc EXCEPT ![p] = "ph2w"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, rcvd>>

Phase2Recv(p, m) ==
  /\ loc[p] = "ph2w"
  /\ m.type = "ph2"
  /\ view[p][m.snd] = Bottom
  /\ view' = [view EXCEPT ![p][m.snd] = m.val]
  /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

DecideMajority(p) ==
  /\ loc[p] = "ph2w"
  /\ \E v \in Values :
       /\ Cardinality({m \in rcvd[p] : m.type = "ph2" /\ m.ev = v}) >= N - T
       /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, rcvd>>

ChooseAlt(p) ==
  /\ loc[p] = "ph2w"
  /\ Cardinality({m \in rcvd[p] : m.type = "ph2"}) = N
  /\ \E v \in Values :
       /\ v \in {view[p][q] : q \in 1..N}
       /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, rcvd>>

ChooseDeterministic(p) ==
  /\ loc[p] = "choose"
  /\ decision' = [decision EXCEPT ![p] = MaxVals({view[p][q] : q \in 1..N})]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, rcvd>>

Crash(p) ==
  /\ crashed < F
  /\ loc[p] # "crashed"
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, decision, sent, rcvd>>

Next ==
  \/ \E p \in 1..N : Phase1Send(p) \/ ComputeEst(p) \/ Phase2Send(p)
                      \/ DecideMajority(p) \/ ChooseAlt(p)
                      \/ ChooseDeterministic(p) \/ Crash(p)
  \/ \E p \in 1..N, m \in sent : Phase1Recv(p, m) \/ Phase2Recv(p, m)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in 1..N, m \in sent : Phase1Recv(p, m))
        /\ WF_vars(\E p \in 1..N, m \in sent : Phase2Recv(p, m))
        /\ WF_vars(\E p \in 1..N : ComputeEst(p))
        /\ WF_vars(\E p \in 1..N : DecideMajority(p))
        /\ WF_vars(\E p \in 1..N : ChooseAlt(p))
        /\ WF_vars(\E p \in 1..N : ChooseDeterministic(p))

TypeOK ==
  /\ loc \in [1..N -> Locations]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ rcvd \in [1..N -> SUBSET Messages]

Validity ==
  \A p \in 1..N : decision[p] # Bottom => decision[p] \in {prop[q] : q \in 1..N}

Agreement ==
  \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Terminate ==
  \A p \in 1..N : loc[p] \in {"done", "crashed"}

ConditionC1 ==
  /\ Cardinality({p \in 1..N : prop[p] = MaxVals({prop[q] : q \in 1..N})}) >= F + 1
  /\ Terminate

====