---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ N > 0
       /\ 2 * T < N
       /\ 0 <= F
       /\ F <= T
       /\ Bottom \notin Values

\* ----------------------------------------------------------------------
\* Process identifiers
\* ----------------------------------------------------------------------
Proc == 1 .. N

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message == [type : {"p1", "p2"},
            sender : Proc,
            value  : Values \cup {Bottom},
            est    : Values \cup {Bottom}]  \* for p1 messages est = Bottom

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* control location of each process
          view,             \* N×N matrix of received values (phase‑1)
          prop,             \* proposed value of each process
          est,              \* estimated value after phase‑1
          estRecv,          \* N×N matrix of received estimated values (phase‑2)
          decision,         \* decision value of each process
          crashed,          \* set of crashed processes
          msgs              \* set of messages that have been sent

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Locs == {"b1", "w1", "b2", "w2", "done", "choose", "crashed"}

MaxVal(S) == 
  CHOOSE v \in S : \A w \in S : w <= v

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Proc |-> "b1"]
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ prop \in [Proc -> Values]                \* each process picks a value
  /\ est = [p \in Proc |-> Bottom]
  /\ estRecv = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ decision = [p \in Proc |-> Bottom]
  /\ crashed = {}
  /\ msgs = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------

\* Phase‑1 broadcast
Broadcast1(p) ==
  /\ pc[p] = "b1"
  /\ pc' = [pc EXCEPT ![p] = "w1"]
  /\ msgs' = msgs \cup {[type |-> "p1", sender |-> p,
                       value |-> prop[p], est |-> Bottom]}
  /\ UNCHANGED <<view, prop, est, estRecv, decision, crashed>>

\* Phase‑1 receive
Receive1(p, q) ==
  /\ pc[p] = "w1"
  /\ \E m \in msgs : m.type = "p1" /\ m.sender = q
  /\ view[p][q] = Bottom
  /\ LET val == CHOOSE v : \E m \in msgs : m.type = "p1" /\ m.sender = q /\ m.value = v
     IN view' = [view EXCEPT ![p][q] = val]
  /\ UNCHANGED <<pc, prop, est, estRecv, decision, crashed, msgs>>

\* Compute estimated value after enough phase‑1 messages
ComputeEst(p) ==
  /\ pc[p] = "w1"
  /\ Cardinality({q \in Proc : view[p][q] # Bottom}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "b2"]
  /\ est' = [est EXCEPT ![p] = 
                MaxVal({view[p][q] : q \in Proc /\ view[p][q] # Bottom})]
  /\ UNCHANGED <<view, prop, estRecv, decision, crashed, msgs>>

\* Phase‑2 broadcast
Broadcast2(p) ==
  /\ pc[p] = "b2"
  /\ pc' = [pc EXCEPT ![p] = "w2"]
  /\ msgs' = msgs \cup {[type |-> "p2", sender |-> p,
                       value |-> prop[p], est |-> est[p]]}
  /\ UNCHANGED <<view, prop, est, estRecv, decision, crashed>>

\* Phase‑2 receive
Receive2(p, q) ==
  /\ pc[p] = "w2"
  /\ \E m \in msgs : m.type = "p2" /\ m.sender = q
  /\ estRecv[p][q] = Bottom
  /\ LET e == CHOOSE v : \E m \in msgs : m.type = "p2" /\ m.sender = q /\ m.est = v
     IN estRecv' = [estRecv EXCEPT ![p][q] = e]
  /\ UNCHANGED <<pc, view, prop, est, decision, crashed, msgs>>

\* Decide when enough identical estimated values are seen
Decide(p) ==
  /\ pc[p] = "w2"
  /\ \E v \in Values :
        Cardinality({q \in Proc : estRecv[p][q] = v}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ UNCHANGED <<view, prop, est, estRecv, crashed, msgs>>

\* Move to choosing state when all phase‑2 messages received but no majority
Choose(p) ==
  /\ pc[p] = "w2"
  /\ \A v \in Values :
        Cardinality({q \in Proc : estRecv[p][q] = v}) < N - T
  /\ \A q \in Proc : estRecv[p][q] # Bottom        \* all N messages received
  /\ LET cand == {view[p][q] : q \in Proc /\ view[p][q] # Bottom}
     IN /\ cand # {}
        /\ pc' = [pc EXCEPT ![p] = "done"]
        /\ decision' = [decision EXCEPT ![p] = MaxVal(cand)]
  /\ UNCHANGED <<view, prop, est, estRecv, crashed, msgs>>

\* Crash a process (up to F faults)
Crash(p) ==
  /\ p \notin crashed
  /\ Cardinality(crashed) < F
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed \cup {p}
  /\ UNCHANGED <<view, prop, est, estRecv, decision, msgs>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Proc : Broadcast1(p)
  \/ \E p,q \in Proc : Receive1(p,q)
  \/ \E p \in Proc : ComputeEst(p)
  \/ \E p \in Proc : Broadcast2(p)
  \/ \E p,q \in Proc : Receive2(p,q)
  \/ \E p \in Proc : Decide(p)
  \/ \E p \in Proc : Choose(p)
  \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<pc, view, prop, est, estRecv, decision, crashed, msgs>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> Locs]
  /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> (Values \cup {Bottom})]
  /\ estRecv \in [Proc -> [Proc -> (Values \cup {Bottom})]]
  /\ decision \in [Proc -> (Values \cup {Bottom})]
  /\ crashed \subseteq Proc
  /\ msgs \subseteq Message

Validity ==
  \A p \in Proc :
    decision[p] # Bottom =>
      /\ decision[p] \in Values
      /\ \E q \in Proc : prop[q] = decision[p]

Agreement ==
  \A p,q \in Proc :
    /\ decision[p] # Bottom
    /\ decision[q] # Bottom
    => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* The required identifiers for the configuration
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

====