---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Process == 0..(N - 1)

VARIABLES location, view, value, estimate, decision, crashed, sent, recv
vars == <<location, view, value, estimate, decision, crashed, sent, recv>>

Locations == {"broadcast1", "wait1", "prepare", "broadcast2", "wait2", "done", "crashed", "choosing"}

RECURSIVE MaxV(_, _)
MaxV(S, f) ==
  IF S = {} THEN Bottom
  ELSE LET x == CHOOSE y \in S : TRUE
       IN LET y == MaxV(S \ {x}, f)
          IN IF f[x] = Bottom THEN y
             ELSE IF y = Bottom THEN f[x]
             ELSE IF f[x] > y THEN f[x] ELSE y

Highest == MaxV(Values, LAMBDA x \in Values : x)

TypeOK ==
  /\ location \in [Process -> Locations]
  /\ view \in [Process -> [Process -> Values \cup {Bottom}]]
  /\ value \in [Process -> Values]
  /\ estimate \in [Process -> Values \cup {Bottom}]
  /\ decision \in [Process -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sent \subseteq [kind: {"phase1", "phase2"}, val: Values \cup {Bottom}, from: Process]
  /\ recv \in [Process -> SUBSET [kind: {"phase1", "phase2"}, val: Values \cup {Bottom}, from: Process]]

Init ==
  /\ location = [p \in Process |-> "broadcast1"]
  /\ view = [p \in Process |-> [q \in Process |-> Bottom]]
  /\ value \in [Process -> Values]
  /\ estimate = [p \in Process |-> Bottom]
  /\ decision = [p \in Process |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in Process |-> {}]

\* Phase 1: broadcast a proposed value.
Broadcast1(p) ==
  /\ location[p] = "broadcast1"
  /\ sent' = sent \cup {[kind |-> "phase1", val |-> value[p], from |-> p]}
  /\ location' = [location EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, value, estimate, decision, crashed, recv>>

\* The network delivers a message to p and p records the sender's value.
Receive(p, m) ==
  /\ location[p] \in {"wait1", "wait2"}
  /\ m.kind = IF location[p] = "wait1" THEN "phase1" ELSE "phase2"
  /\ m.from \notin recv[p]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ UNCHANGED <<location, value, estimate, decision, crashed, sent>>

\* Having heard from enough senders, p computes its estimated value.
Estimate(p) ==
  /\ location[p] = "wait1"
  /\ Cardinality({m \in recv[p] : m.kind = "phase1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = MaxV(Process, LAMBDA q \in Process : view[p][q])]
  /\ location' = [location EXCEPT ![p] = "prepare"]
  /\ UNCHANGED <<view, value, decision, crashed, sent, recv>>

\* Phase 2: broadcast both the proposed and the estimated value.
Broadcast2(p) ==
  /\ location[p] = "prepare"
  /\ sent' = sent \cup {[kind |-> "phase2", val |-> estimate[p], from |-> p]}
  /\ location' = [location EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, value, estimate, decision, crashed, recv>>

\* If enough messages agree on an estimated value, decide it.
Decide(p) ==
  /\ location[p] = "wait2"
  /\ \E val \in Values :
       /\ Cardinality({m \in recv[p] : m.kind = "phase2" /\ m.val = val}) >= N - T
       /\ decision' = [decision EXCEPT ![p] = val]
  /\ location' = [location EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, value, estimate, crashed, sent, recv>>

\* Without an agreed-upon estimate, p chooses some value it has seen.
Choose(p) ==
  /\ location[p] = "wait2"
  /\ \A v \in Values : Cardinality({m \in recv[p] : m.kind = "phase2" /\ m.val = v}) < N - T
  /\ \E val \in Values :
       /\ \E q \in Process : view[p][q] = val /\ decision' = [decision EXCEPT ![p] = val]
  /\ location' = [location EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, value, estimate, crashed, sent, recv>>

FinishChoosing(p) ==
  /\ location[p] = "choosing"
  /\ decision[p] # Bottom
  /\ location' = [location EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, value, estimate, crashed, sent, recv, decision>>

Crash(p) ==
  /\ crashed < F
  /\ location[p] \notin {"crashed", "done"}
  /\ crashed' = crashed + 1
  /\ location' = [location EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<view, value, estimate, decision, sent, recv>>

Done == \A p \in Process : location[p] \in {"done", "crashed"}

Next ==
  \/ \E p \in Process : Broadcast1(p) \/ Estimate(p) \/ Broadcast2(p) \/ Decide(p)
  \/ \E p \in Process, m \in sent : Receive(p, m)
  \/ \E p \in Process : Choose(p) \/ FinishChoosing(p) \/ Crash(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Process, m \in sent : Receive(p, m))
  /\ WF_vars(\E p \in Process : Estimate(p))
  /\ WF_vars(\E p \in Process : Decide(p)
  /\ WF_vars(\E p \in Process : Choose(p))
  /\ WF_vars(\E p \in Process : FinishChoosing(p))

Validity == \A p \in Process : decision[p] # Bottom => decision[p] \in Values

Agreement == \A p, q \in Process : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination == Done

\* Under Condition C1 (enough max-value proponents) the protocol must finish.
ConditionalTermination ==
  /\ {p \in Process : value[p] = Highest} \subseteq {p \in Process : decision[p] = Highest}
  /\ Cardinality({p \in Process : value[p] = Highest}) >= F + 1
  => Done
====