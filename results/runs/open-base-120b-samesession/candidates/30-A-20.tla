---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Proc   == 1 .. N
Locs   == {"bcast1", "wait1", "bcast2", "wait2", "choosing", "done", "crashed"}

Msg    == [type : {"p1","p2"}, sender : Proc, value : Values, est : Values]

MaxVal(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE v \in S : \A w \in S : w <= v

ReceivedFrom(p) ==
    { m.sender : m \in recv[p] /\ m.type = "p1" }

CountEst(p, v) ==
    Cardinality({ m \in recv[p] : m.type = "p2" /\ m.est = v })

AllPhase2Received(p) ==
    \A q \in Proc : \E m \in recv[p] :
        /\ m.type = "p2"
        /\ m.sender = q

Candidates(p) ==
    { view[p][q] : q \in Proc /\ view[p][q] # Bottom }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES loc, view, prop, est, decision, crashed, msgs, recv

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ loc = [p \in Proc |-> "bcast1"]
    /\ prop \in [Proc -> Values]                 \* nondeterministic proposal
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ decision = [p \in Proc |-> Bottom]
    /\ crashed = {}
    /\ msgs = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Phase‑1 actions
\* ----------------------------------------------------------------------
Phase1Broadcast(p) ==
    /\ loc[p] = "bcast1"
    /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ msgs' = msgs \cup {
            [type |-> "p1", sender |-> p,
             value |-> prop[p], est |-> Bottom]
        }
    /\ UNCHANGED <<view, prop, est, decision, crashed, recv>>

Phase1Receive(p) ==
    \E m \in msgs :
        /\ m.type = "p1"
        /\ m \notin recv[p]
        /\ loc[p] = "wait1"
        /\ view' = [view EXCEPT ![p][m.sender] = m.value]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
        /\ UNCHANGED <<loc, prop, est, decision, crashed, msgs>>

Phase1Compute(p) ==
    /\ loc[p] = "wait1"
    /\ Cardinality(ReceivedFrom(p)) >= N - T
    /\ loc' = [loc EXCEPT ![p] = "bcast2"]
    /\ est' = [est EXCEPT ![p] = MaxVal({ view[p][q] : q \in Proc })]
    /\ UNCHANGED <<view, prop, decision, crashed, msgs, recv>>

\* ----------------------------------------------------------------------
\* Phase‑2 actions
\* ----------------------------------------------------------------------
Phase2Broadcast(p) ==
    /\ loc[p] = "bcast2"
    /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ msgs' = msgs \cup {
            [type |-> "p2", sender |-> p,
             value |-> prop[p], est |-> est[p]]
        }
    /\ UNCHANGED <<view, prop, est, decision, crashed, recv>>

Phase2Receive(p) ==
    \E m \in msgs :
        /\ m.type = "p2"
        /\ m \notin recv[p]
        /\ loc[p] = "wait2"
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
        /\ UNCHANGED <<loc, view, prop, est, decision, crashed, msgs>>

Phase2Decide(p) ==
    /\ loc[p] = "wait2"
    /\ \E v \in Values :
          CountEst(p, v) >= N - T
    /\ LET v == CHOOSE w \in Values :
               CountEst(p, w) >= N - T
       IN
          /\ decision' = [decision EXCEPT ![p] = v]
          /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, msgs, recv>>

Phase2AllReceived(p) ==
    /\ loc[p] = "wait2"
    /\ AllPhase2Received(p)
    /\ \A v \in Values : CountEst(p, v) < N - T
    /\ loc' = [loc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, prop, est, decision, crashed, msgs, recv>>

Choosing(p) ==
    /\ loc[p] = "choosing"
    /\ Candidates(p) # {}
    /\ decision' = [decision EXCEPT ![p] = CHOOSE v \in Candidates(p) : TRUE]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, msgs, recv>>

\* ----------------------------------------------------------------------
\* Crash action
\* ----------------------------------------------------------------------
Crash(p) ==
    /\ p \notin crashed
    /\ Cardinality(crashed) < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<view, prop, est, decision, msgs, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : Phase1Broadcast(p)
    \/ \E p \in Proc : Phase1Receive(p)
    \/ \E p \in Proc : Phase1Compute(p)
    \/ \E p \in Proc : Phase2Broadcast(p)
    \/ \E p \in Proc : Phase2Receive(p)
    \/ \E p \in Proc : Phase2Decide(p)
    \/ \E p \in Proc : Phase2AllReceived(p)
    \/ \E p \in Proc : Choosing(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<loc, view, prop, est, decision, crashed, msgs, recv>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ loc \in [Proc -> Locs]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ decision \in [Proc -> (Values \cup {Bottom})]
    /\ crashed \subseteq Proc
    /\ msgs \subseteq Msg
    /\ recv \in [Proc -> SUBSET Msg]
    /\ Bottom \notin Values

Validity ==
    \A p \in Proc :
        decision[p] # Bottom =>
            decision[p] \in { prop[q] : q \in Proc }

Agreement ==
    \A p, q \in Proc :
        (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* Exported identifiers
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

=============================================================================