---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME 2 * T < N
ASSUME N \in Nat /\ N > 0
ASSUME 0 <= F /\ F <= T
ASSUME Bottom \notin Values

MessageTypes == {"phase1", "phase2"}

VARIABLES loc, localView, proposal, estimate, decision, crashed, messages, received
vars == <<loc, localView, proposal, estimate, decision, crashed, messages, received>>

RECURSIVE MaxOf(_, _)
MaxOf(domain, f) ==
  IF domain = {} THEN Bottom
  ELSE LET x == CHOOSE y \in domain : TRUE IN
    LET fx == f[x] IN
    LET rest == MaxOf(domain \ {x}, f) IN
    IF fx > rest THEN fx ELSE rest

\* A process may only transition on a phase it is actually in; crashed
\* processes are excluded from every other rule.
Participating(p) == loc[p] \notin {"crashed", "done"}

Init ==
  /\ loc = [p \in 1..N |-> "bc1"]
  /\ localView = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ proposal \in [p \in 1..N |-> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ messages = {}
  /\ received = [p \in 1..N |-> {}]

SendPhase1(p) ==
  /\ loc[p] = "bc1"
  /\ messages' = messages \cup {[type |-> "phase1", val |-> proposal[p], from |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<localView, proposal, estimate, decision, crashed, received>>

\* Each message from a sender is folded into the local view, never dropping
\* information that has already landed.
ReceivePhase1(p, m) ==
  /\ loc[p] = "w1"
  /\ m \in messages
  /\ m.type = "phase1"
  /\ m.from \notin received[p]
  /\ localView' = [localView EXCEPT ![p][m.from] = m.val]
  /\ received' = [received EXCEPT ![p] = @ \cup {m.from}]
  /\ UNCHANGED <<loc, proposal, estimate, decision, crashed, messages>>

BroadcastPhase2(p) ==
  /\ loc[p] = "w1"
  /\ Cardinality(received[p]) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = MaxOf(1..N, LAMBDA q : localView[p][q])]
  /\ messages' = messages \cup {[type |-> "phase2", val |-> proposal[p], est |-> estimate[p], from |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "bc2"]
  /\ UNCHANGED <<localView, proposal, decision, crashed, received>>

ReceivePhase2(p, m) ==
  /\ loc[p] = "bc2"
  /\ m \in messages
  /\ m.type = "phase2"
  /\ m.from \notin received[p]
  /\ received' = [received EXCEPT ![p] = @ \cup {m.from}]
  /\ UNCHANGED <<loc, localView, proposal, estimate, decision, crashed, messages>>

DecideByThreshold(p, v) ==
  /\ loc[p] = "bc2"
  /\ Cardinality({m \in messages : m.type = "phase2" /\ m.est = v}) >= N - T
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<localView, proposal, estimate, crashed, messages, received>>

ChooseArbitrary(p) ==
  /\ loc[p] = "bc2"
  /\ Cardinality(received[p]) = N
  /\ \A v \in Values : Cardinality({m \in messages : m.type = "phase2" /\ m.est = v}) < N - T
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<localView, proposal, estimate, decision, crashed, messages, received>>

DecideByChoosing(p, v) ==
  /\ loc[p] = "choose"
  /\ v \in {localView[p][q] : q \in 1..N}
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<localView, proposal, estimate, crashed, messages, received>>

Crash(p) ==
  /\ crashed < F
  /\ loc[p] # "crashed"
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<localView, proposal, estimate, decision, messages, received>>

Next ==
  \/ \E p \in 1..N :
       SendPhase1(p) \/ BroadcastPhase2(p) \/ ChooseArbitrary(p) \/ Crash(p)
  \/ \E p \in 1..N, m \in messages : ReceivePhase1(p, m) \/ ReceivePhase2(p, m)
  \/ \E p \in 1..N, v \in Values : DecideByThreshold(p, v) \/ DecideByChoosing(p, v)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N, m \in messages : ReceivePhase1(p, m))
  /\ WF_vars(\E p \in 1..N, m \in messages : ReceivePhase2(p, m))
  /\ WF_vars(\E p \in 1..N : BroadcastPhase2(p))
  /\ WF_vars(\E p \in 1..N : ChooseArbitrary(p))
  /\ WF_vars(\E p \in 1..N, v \in Values : DecideByThreshold(p, v))
  /\ WF_vars(\E p \in 1..N, v \in Values : DecideByChoosing(p, v))

TypeOK ==
  /\ loc \in [1..N -> {"bc1", "w1", "bc2", "choose", "done", "crashed"}]
  /\ localView \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposal \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ messages \subseteq [type : MessageTypes, val : Values, est : Values \cup {Bottom}, from : 1..N]
  /\ received \in [1..N -> SUBSET (1..N)]

Validity == \A p \in 1..N : decision[p] # Bottom => \E q \in 1..N : proposal[q] = decision[p]

Agreement == \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

\* Every process either crashes or finishes with a decision.
Termination == \A p \in 1..N : loc[p] \in {"done", "crashed"}

\* Under Condition C1 the protocol must terminate regardless of order.
ConditionalTermination ==
  ((\E S \in SUBSET (1..N) : Cardinality(S) >= F + 1 /\ \A p \in S : proposal[p] = MaxOf(1..N, proposal))
   /\ \A p \in 1..N : loc[p] = "done")

INVARIANT TypeOK
INVARIANT Validity
INVARIANT Agreement
PROPERTY Termination
PROPERTY ConditionalTermination
====