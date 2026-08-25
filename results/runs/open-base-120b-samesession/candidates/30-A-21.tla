---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ 0 < N
        /\ 2 * T < N
        /\ 0 <= F
        /\ F <= T
        /\ Bottom \\in Values  \* Bottom is distinct from real values (will be excluded later)
        /\ Bottom \\notin Values
        /\ VALUES = Values
        /\ IsFinite(Values)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == 1 .. N

Locs == {"broad1", "wait1", "broad2", "wait2", "done", "crashed", "choosing"}

Msg == [type   : {"phase1","phase2"},
        sender : Proc,
        value  : Values,
        est    : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES loc,                     \* [p \in Proc -> Locs]
          view,                    \* [p \in Proc -> [q \in Proc -> Values \cup {Bottom}]]
          prop,                    \* [p \in Proc -> Values]
          est,                     \* [p \in Proc -> Values \cup {Bottom}]
          dec,                     \* [p \in Proc -> Values \cup {Bottom}]
          crashed,                 \* SUBSET Proc
          msgs,                    \* SUBSET Msg
          estView                  \* [p \in Proc -> [q \in Proc -> Values \cup {Bottom}]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Max(S) == 
  IF S = {} THEN Bottom 
  ELSE CHOOSE x \in S : \A y \in S : y <= x

\* Count of distinct senders from which a process p has a non‑Bottom entry
RecvCount(p, mat) == 
  Cardinality({ q \in Proc : mat[p][q] # Bottom })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
 /\ loc = [p \in Proc |-> "broad1"]
 /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
 /\ prop \in [Proc -> Values]   \* each process chooses an initial proposal
 /\ est = [p \in Proc |-> Bottom]
 /\ dec = [p \in Proc |-> Bottom]
 /\ crashed = {}
 /\ msgs = {}
 /\ estView = [p \in Proc |-> [q \in Proc |-> Bottom]]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
 /\ p \in Proc
 /\ loc[p] = "broad1"
 /\ p \notin crashed
 /\ UNCHANGED <<view, est, dec, crashed, estView>>
 /\ loc' = [loc EXCEPT ![p] = "wait1"]
 /\ msgs' = msgs \cup { [type |-> "phase1", sender |-> p,
                        value |-> prop[p], est |-> Bottom] }

ReceivePhase1(p, m) ==
 /\ p \in Proc
 /\ m \in msgs
 /\ m.type = "phase1"
 /\ loc[p] = "wait1"
 /\ p \notin crashed
 /\ view' = [view EXCEPT ![p][m.sender] = m.value]
 /\ UNCHANGED <<loc, prop, est, dec, crashed, msgs, estView>>

ComputeEst(p) ==
 /\ p \in Proc
 /\ loc[p] = "wait1"
 /\ p \notin crashed
 /\ RecvCount(p, view) >= N - T
 /\ LET vals == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
    est' = [est EXCEPT ![p] = Max(vals)]
 /\ loc' = [loc EXCEPT ![p] = "broad2"]
 /\ UNCHANGED <<view, prop, dec, crashed, msgs, estView>>

BroadcastPhase2(p) ==
 /\ p \in Proc
 /\ loc[p] = "broad2"
 /\ p \notin crashed
 /\ UNCHANGED <<view, est, dec, crashed, msgs, estView>>
 /\ loc' = [loc EXCEPT ![p] = "wait2"]
 /\ msgs' = msgs \cup { [type |-> "phase2", sender |-> p,
                        value |-> prop[p], est |-> est[p]] }

ReceivePhase2(p, m) ==
 /\ p \in Proc
 /\ m \in msgs
 /\ m.type = "phase2"
 /\ loc[p] = "wait2"
 /\ p \notin crashed
 /\ view' = [view EXCEPT ![p][m.sender] = m.value]
 /\ estView' = [estView EXCEPT ![p][m.sender] = m.est]
 /\ UNCHANGED <<loc, prop, est, dec, crashed, msgs>>

Decide(p, v) ==
 /\ p \in Proc
 /\ loc[p] = "wait2"
 /\ p \notin crashed
 /\ v \in Values
 /\ Cardinality({ q \in Proc : estView[p][q] = v }) >= N - T
 /\ dec' = [dec EXCEPT ![p] = v]
 /\ loc' = [loc EXCEPT ![p] = "done"]
 /\ UNCHANGED <<view, prop, est, crashed, msgs, estView>>

MoveChoosing(p) ==
 /\ p \in Proc
 /\ loc[p] = "wait2"
 /\ p \notin crashed
 /\ \A q \in Proc : estView[p][q] # Bottom   \* all N phase‑2 messages received
 /\ \A v \in Values : Cardinality({ q \in Proc : estView[p][q] = v }) < N - T
 /\ loc' = [loc EXCEPT ![p] = "choosing"]
 /\ UNCHANGED <<view, prop, est, dec, crashed, msgs, estView>>

Choose(p) ==
 /\ p \in Proc
 /\ loc[p] = "choosing"
 /\ p \notin crashed
 /\ LET vals == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
    vals # {}   \* there is at least one known value
 /\ let chosen == Max(vals) in
    dec' = [dec EXCEPT ![p] = chosen]
 /\ loc' = [loc EXCEPT ![p] = "done"]
 /\ UNCHANGED <<view, prop, est, crashed, msgs, estView>>

Crash(p) ==
 /\ p \in Proc
 /\ p \notin crashed
 /\ Cardinality(crashed) < F
 /\ crashed' = crashed \cup {p}
 /\ loc' = [loc EXCEPT ![p] = "crashed"]
 /\ UNCHANGED <<view, prop, est, dec, msgs, estView>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
 \/ \E p \in Proc : BroadcastPhase1(p)
 \/ \E p \in Proc, m \in msgs : ReceivePhase1(p,m)
 \/ \E p \in Proc : ComputeEst(p)
 \/ \E p \in Proc : BroadcastPhase2(p)
 \/ \E p \in Proc, m \in msgs : ReceivePhase2(p,m)
 \/ \E p \in Proc, v \in Values : Decide(p,v)
 \/ \E p \in Proc : MoveChoosing(p)
 \/ \E p \in Proc : Choose(p)
 \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<loc, view, prop, est, dec, crashed, msgs, estView>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
 /\ loc \in [Proc -> Locs]
 /\ view \in [Proc -> [Proc -> Values \cup {Bottom}]]
 /\ prop \in [Proc -> Values]
 /\ est \in [Proc -> Values \cup {Bottom}]
 /\ dec \in [Proc -> Values \cup {Bottom}]
 /\ crashed \subseteq Proc
 /\ msgs \subseteq Msg
 /\ estView \in [Proc -> [Proc -> Values \cup {Bottom}]]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
 \A p \in Proc :
   dec[p] # Bottom => 
     (\E q \in Proc : prop[q] = dec[p])

Agreement ==
 \A p, q \in Proc :
   /\ dec[p] # Bottom
   /\ dec[q] # Bottom
   => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====