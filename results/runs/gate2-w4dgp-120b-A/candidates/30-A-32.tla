---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, proposal, estimate, decision, crashed, sent, received
vars == <<loc, view, proposal, estimate, decision, crashed, sent, received>>

StateSpace == Values \cup {Bottom}
Bump(x) == IF x = Bottom THEN 0 ELSE x
MaxOf(S) == IF S = {} THEN 0 ELSE LET m == CHOOSE x \in S : \A y \in S : y <= x IN m
SatisfiesC1 == Cardinality({p \in 1 .. N : proposal[p] = MaxOf(Values)}) >= (F + 1)

TypeOK ==
  /\ loc \in [1 .. N -> {"br1", "w1", "prep", "br2", "w2", "done", "crashed", "choosing"}]
  /\ view \in [1 .. N -> [1 .. N -> StateSpace]]
  /\ proposal \in [1 .. N -> Values]
  /\ estimate \in [1 .. N -> StateSpace]
  /\ decision \in [1 .. N -> StateSpace]
  /\ crashed \in 0 .. F
  /\ sent \subseteq [type: {"p1", "p2"}, value: Values, from: 1 .. N]
  /\ received \in [1 .. N -> SUBSET [type: {"p1", "p2"}, value: Values, from: 1 .. N]]

Init ==
  /\ loc = [p \in 1 .. N |-> "br1"]
  /\ view = [p \in 1 .. N |-> [q \in 1 .. N |-> Bottom]]
  /\ proposal \in [1 .. N -> Values]
  /\ estimate = [p \in 1 .. N |-> Bottom]
  /\ decision = [p \in 1 .. N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [p \in 1 .. N |-> {}]

BroadcastP1(p) ==
  /\ loc[p] = "br1"
  /\ sent' = sent \cup {[type |-> "p1", value |-> proposal[p], from |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, received>>

ReceiveP1(p, m) ==
  /\ loc[p] \in {"w1", "w2"}
  /\ m.type = "p1"
  /\ m \notin received[p]
  /\ view[p][m.from] = Bottom
  /\ view' = [view EXCEPT ![p][m.from] = m.value]
  /\ received' = [received EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<loc, proposal, estimate, decision, crashed, sent>>

ComputeEstimate(p) ==
  /\ loc[p] = "w1"
  /\ Cardinality({m \in received[p] : m.type = "p1"}) >= (N - T)
  /\ estimate' = [estimate EXCEPT ![p] = MaxOf({view[p][q] : q \in 1 .. N})]
  /\ loc' = [loc EXCEPT ![p] = "br2"]
  /\ UNCHANGED <<view, proposal, decision, crashed, sent, received>>

BroadcastP2(p) ==
  /\ loc[p] = "br2"
  /\ sent' = sent \cup {[type |-> "p2", value |-> proposal[p], from |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "w2"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, received>>

DecideByThreshold(p) ==
  /\ loc[p] = "w2"
  /\ \E x \in Values :
      /\ Cardinality({m \in received[p] : m.type = "p2" /\ estimate[m.from] = x}) >= (N - T)
      /\ decision' = [decision EXCEPT ![p] = x]
      /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, sent, received>>

Choose(p) ==
  /\ loc[p] = "w2"
  /\ \A m \in received[p] : m.type = "p2"
  /\ Cardinality({m \in received[p] : m.type = "p2"}) = N
  /\ \A x \in Values : Cardinality({m \in received[p] : m.type = "p2" /\ estimate[m.from] = x}) < (N - T)
  /\ \E x \in Values :
       /\ Cardinality({q \in 1 .. N : view[p][q] = x}) >= 1
       /\ decision' = [decision EXCEPT ![p] = x]
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, sent, received>>

Crash(p) ==
  /\ crashed < F
  /\ loc[p] # "crashed"
  /\ crashed' = crashed + 1
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<view, proposal, estimate, decision, sent, received>>

Next ==
  \/ \E p \in 1 .. N :
        BroadcastP1(p) \/ BroadcastP2(p) \/ ComputeEstimate(p) \/ Crash(p)
  \/ \E p \in 1 .. N, m \in sent : ReceiveP1(p, m)
  \/ \E p \in 1 .. N : DecideByThreshold(p) \/ Choose(p)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in 1 .. N : BroadcastP1(p))
  /\ WF_vars(\E p \in 1 .. N, m \in sent : ReceiveP1(p, m))
  /\ WF_vars(\E p \in 1 .. N : ComputeEstimate(p))
  /\ WF_vars(\E p \in 1 .. N : BroadcastP2(p))
  /\ WF_vars(\E p \in 1 .. N : DecideByThreshold(p))
  /\ WF_vars(\E p \in 1 .. N : Choose(p))

Validity == \A p \in 1 .. N : decision[p] # Bottom => \E q \in 1 .. N : proposal[q] = decision[p]

Agreement == \A p, q \in 1 .. N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination == <>(\A p \in 1 .. N : loc[p] \in {"crashed", "done", "choosing"})

TermC1 == SatisfiesC1 ~> (\A p \in 1 .. N : loc[p] \in {"crashed", "done", "choosing"})

====