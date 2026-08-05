---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME N \in Nat /\ N > 0 /\ T \in Nat /\ F \in Nat /\ T >= F /\ 2 * T < N
ASSUME Bottom \notin Values
ASSUME \E x \in Values : \A y \in Values : x >= y

VARIABLES loc, view, proposal, estimate, decided, crashed, sent, rx

vars == <<loc, view, proposal, estimate, decided, crashed, sent, rx>>

Phases == {"bcast1", "wait1", "prep2", "bcast2", "wait2", "done", "crashed", "choose"}
Types == {"p1", "p2"}
Msgs == [type : Types, val : Values, snd : 0 .. (N - 1), est : Values \cup {Bottom}]

MaxOf(v) == LET g[S \in SUBSET Values] ==
                IF S = {} THEN Bottom
                ELSE LET x == CHOOSE y \in S : \A z \in S : y >= z
                     IN x
            IN g(v)

Init ==
  /\ loc = [p \in 0 .. (N - 1) |-> "bcast1"]
  /\ view = [p \in 0 .. (N - 1) |-> [q \in 0 .. (N - 1) |-> Bottom]]
  /\ proposal \in [p \in 0 .. (N - 1) |-> Values]
  /\ estimate = [p \in 0 .. (N - 1) |-> Bottom]
  /\ decided = [p \in 0 .. (N - 1) |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ rx = [p \in 0 .. (N - 1) |-> {}]

Bcast1(p) ==
  /\ loc[p] = "bcast1"
  /\ sent' = sent \cup {[type |-> "p1", val |-> proposal[p], snd |-> p, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, proposal, estimate, decided, crashed, rx>>

Receive1(p) ==
  /\ loc[p] = "wait1"
  /\ \E m \in sent :
       /\ m.type = "p1"
       /\ m.snd \notin rx[p]
       /\ view' = [view EXCEPT ![p][m.snd] = m.val]
       /\ rx' = [rx EXCEPT ![p] = rx[p] \cup {m.snd}]
  /\ UNCHANGED <<loc, proposal, estimate, decided, crashed, sent>>

Compute(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality(rx[p]) >= (N - T)
  /\ estimate' = [estimate EXCEPT ![p] = MaxOf(view[p])]
  /\ loc' = [loc EXCEPT ![p] = "bcast2"]
  /\ UNCHANGED <<view, proposal, decided, crashed, sent, rx>>

Bcast2(p) ==
  /\ loc[p] = "bcast2"
  /\ sent' = sent \cup {[type |-> "p2", val |-> proposal[p], snd |-> p, est |-> estimate[p]]}
  /\ loc' = [loc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, proposal, estimate, decided, crashed, rx>>

Receive2(p) ==
  /\ loc[p] = "wait2"
  /\ \E m \in sent :
       /\ m.type = "p2"
       /\ view' = [view EXCEPT ![p][m.snd] = m.est]
       /\ rx' = [rx EXCEPT ![p] = rx[p] \cup {m.snd}]
  /\ UNCHANGED <<loc, proposal, estimate, decided, crashed, sent>>

Decide(p) ==
  /\ loc[p] = "wait2"
  /\ \E v \in Values :
       /\ Cardinality({q \in 0 .. (N - 1) : view[p][q] = v}) >= (N - T)
       /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, sent, rx>>

Choose(p) ==
  /\ loc[p] = "wait2"
  /\ \A q \in 0 .. (N - 1) : q \in rx[p]
  /\ \E v \in Values :
       /\ Cardinality({q \in 0 .. (N - 1) : view[p][q] = v}) > 0
       /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, sent, rx>>

Crash(p) ==
  /\ crashed < F
  /\ loc[p] # "crashed"
  /\ crashed' = crashed + 1
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<view, proposal, estimate, decided, sent, rx>>

Next ==
  \/ \E p \in 0 .. (N - 1) : Bcast1(p) \/ Receive1(p) \/ Compute(p)
                           \/ Bcast2(p) \/ Receive2(p) \/ Decide(p)
                           \/ Choose(p) \/ Crash(p)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(\E p \in 0 .. (N - 1) : Crash(p))
        /\ WF_vars(\E p \in 0 .. (N - 1) : Bcast1(p))
        /\ WF_vars(\E p \in 0 .. (N - 1) : Receive1(p))
        /\ WF_vars(\E p \in 0 .. (N - 1) : Compute(p))
        /\ WF_vars(\E p \in 0 .. (N - 1) : Bcast2(p))
        /\ WF_vars(\E p \in 0 .. (N - 1) : Receive2(p))
        /\ WF_vars(\E p \in 0 .. (N - 1) : Decide(p))
        /\ WF_vars(\E p \in 0 .. (N - 1) : Choose(p))

TypeOK ==
  /\ loc \in [0 .. (N - 1) -> Phases]
  /\ view \in [0 .. (N - 1) -> [0 .. (N - 1) -> Values \cup {Bottom}]]
  /\ proposal \in [0 .. (N - 1) -> Values]
  /\ estimate \in [0 .. (N - 1) -> Values \cup {Bottom}]
  /\ decided \in [0 .. (N - 1) -> Values \cup {Bottom}]
  /\ crashed \in 0 .. F
  /\ sent \subseteq Msgs
  /\ rx \in [0 .. (N - 1) -> SUBSET (0 .. (N - 1))]

Validity ==
  \A p \in 0 .. (N - 1) : decided[p] # Bottom => \E q \in 0 .. (N - 1) : proposal[q] = decided[p]

Agreement ==
  \A p, q \in 0 .. (N - 1) : (decided[p] # Bottom /\ decided[p] = decided[q]) => decided[p] = decided[q]

Terminate ==
  \A p \in 0 .. (N - 1) : loc[p] \in {"done", "crashed"}

Conditioned ==
  (Cardinality({p \in 0 .. (N - 1) : proposal[p] = MaxOf({q \in 0 .. (N - 1) : proposal[q]})})
     >= (F + 1))
    => Terminate

====