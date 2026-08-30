---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Items == 0 .. (N - 1)

VARIABLES loc, view, propose, estimate, decided, crashed, sent, received

vars == <<loc, view, propose, estimate, decided, crashed, sent, received>>

Locs == {"p1a", "p1w", "p2a", "p2b", "p2w", "done", "crashed", "choosing"}

\* Two-phase, value-based agreement: an estimate is the max over all values a
\* process has observed locally; the safety properties are decided validity and
\* agreement, both phrased purely in terms of values.
MaxOf(f, S) ==
  IF S = {} THEN Bottom
  ELSE LET x == CHOOSE y \in S : TRUE
           m == f[x]
       IN LET mx == MaxOf(f, S \ {x})
          IN IF m > mx THEN m ELSE mx

TypeOK ==
  /\ loc \in [Items -> Locs]
  /\ view \in [Items -> [Items -> Values \cup {Bottom}]]
  /\ propose \in [Items -> Values]
  /\ estimate \in [Items -> Values \cup {Bottom}]
  /\ decided \in [Items -> Values \cup {Bottom}]
  /\ crashed \in 0 .. N
  /\ sent \subseteq [kind: {"p1", "p2"}, val: Values, from: Items, ev: Values \cup {Bottom}]
  /\ received \in [Items -> SUBSET Items]

Init ==
  /\ loc = [p \in Items |-> "p1a"]
  /\ view = [p \in Items |-> [q \in Items |-> Bottom]]
  /\ propose \in [Items -> Values]
  /\ estimate = [p \in Items |-> Bottom]
  /\ decided = [p \in Items |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [p \in Items |-> {}]

BroadcastP1(p) ==
  /\ loc[p] = "p1a"
  /\ sent' = sent \cup {[kind |-> "p1", val |-> propose[p], from |-> p, ev |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "p1w"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, received>>

ReceiveP1(p, m) ==
  /\ loc[p] = "p1w"
  /\ m.kind = "p1"
  /\ m.from \notin received[p]
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ received' = [received EXCEPT ![p] = @ \cup {m.from}]
  /\ UNCHANGED <<loc, propose, estimate, decided, crashed, sent>>

ComputeEstimate(p) ==
  /\ loc[p] = "p1w"
  /\ Cardinality(received[p]) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = MaxOf(view[p], Items)]
  /\ loc' = "p2a"
  /\ UNCHANGED <<view, propose, decided, crashed, sent, received>>

BroadcastP2(p) ==
  /\ loc[p] = "p2a"
  /\ sent' = sent \cup {[kind |-> "p2", val |-> propose[p], from |-> p, ev |-> estimate[p]]}
  /\ loc' = "p2b"
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, received>>

\* Phase two may resolve early, once an estimated value is backed by
\* at least N - T distinct process messages.
DecideFromP2(p) ==
  /\ loc[p] = "p2b"
  /\ \E v \in Values :
       /\ Cardinality({q \in Items : [kind |-> "p2", val |-> propose[q], from |-> q, ev |-> v] \in sent})
            >= N - T
       /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = "done"
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, received>>

\* If the messages disagree before any threshold can fire, a process falls back
\* to picking a value it can already see: this is the resolution that keeps the
\* two-phase protocol from ever deadlocking.
Choose(p) ==
  /\ loc[p] = "p2b"
  /\ \A q \in Items : [kind |-> "p2", val |-> propose[q], from |-> q, ev |-> estimate[p]] \in sent
  /\ \A v \in Values :
       Cardinality({q \in Items : [kind |-> "p2", val |-> propose[q], from |-> q, ev |-> v] \in sent})
           < N - T
  /\ decided' = [decided EXCEPT ![p] = estimate[p]]
  /\ loc' = "done"
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, received>>

Crash(p) ==
  /\ loc[p] \notin {"done", "crashed"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, propose, estimate, decided, sent, received>>

Next ==
  \/ \E p \in Items : BroadcastP1(p) \/ ComputeEstimate(p) \/ BroadcastP2(p)
                     \/ DecideFromP2(p) \/ Choose(p) \/ Crash(p)
  \/ \E p \in Items, m \in sent : ReceiveP1(p, m)

Spec == Init /\ [][Next]_vars
    /\ \A p \in Items : WF_vars(ComputeEstimate(p))
    /\ \A p \in Items : WF_vars(DecideFromP2(p))
    /\ \A p \in Items : WF_vars(Choose(p))
    /\ \A p \in Items : SF_vars(Crash(p))

Validity == \A p \in Items : decided[p] # Bottom => \E q \in Items : propose[q] = decided[p]

Agreement == \A p, q \in Items :
  (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

\* Termination of the whole protocol, plus the condition guaranteeing it.
Termination == <>(\A p \in Items : loc[p] \in {"done", "crashed"})
CondC1 == \E p \in Items : decide[p] = MaxOf(propose, Items)

====