---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Process set
\* ----------------------------------------------------------------------
Proc == 1 .. N

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message == [type : {"ph1", "ph2"},
            sender : Proc,
            val    : Values,
            est    : Values]  \* est is meaningful only for "ph2" messages

\* ----------------------------------------------------------------------
\* Helper: maximum of a non‑empty set of Values (Bottom otherwise)
\* ----------------------------------------------------------------------
Max(S) == 
    IF S = {} THEN Bottom
    ELSE CHOOSE v \in S : \A w \in S : w <= v

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* control state of each process
          view,             \* local view matrix of values
          prop,             \* proposed value of each process
          est,              \* estimated value after phase 1
          dec,              \* decision value
          msgs,             \* set of messages in the network
          estReceived       \* for each process, map estimated values to senders

vars == <<pc, view, prop, est, dec, msgs, estReceived>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "bcast1"]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ prop \in [Proc -> Values]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ msgs = {}
    /\ estReceived = [p \in Proc |-> [v \in Values |-> {}]]

\* ----------------------------------------------------------------------
\* Phase 1 actions
\* ----------------------------------------------------------------------
Bcast1(p) ==
    /\ pc[p] = "bcast1"
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ msgs' = msgs \cup { [type |-> "ph1",
                           sender |-> p,
                           val    |-> prop[p],
                           est    |-> Bottom] }
    /\ UNCHANGED <<view, prop, est, dec, estReceived>>

Receive1(p, q) ==
    /\ pc[p] = "wait1"
    /\ view[p][q] = Bottom
    /\ \E m \in msgs :
          /\ m.type = "ph1"
          /\ m.sender = q
          /\ m.val = prop[q]
          /\ view' = [view EXCEPT ![p][q] = m.val]
    /\ UNCHANGED <<pc, prop, est, dec, msgs, estReceived>>

Phase1Complete(p) ==
    /\ pc[p] = "wait1"
    /\ Cardinality({ q \in Proc : view[p][q] # Bottom }) >= N - T
    /\ est' = [est EXCEPT ![p] = Max({ view[p][q] : q \in Proc })]
    /\ pc' = [pc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED <<view, prop, dec, msgs, estReceived>>

Bcast2(p) ==
    /\ pc[p] = "bcast2"
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ msgs' = msgs \cup { [type |-> "ph2",
                           sender |-> p,
                           val    |-> prop[p],
                           est    |-> est[p]] }
    /\ UNCHANGED <<view, prop, est, dec, estReceived>>

\* ----------------------------------------------------------------------
\* Phase 2 actions
\* ----------------------------------------------------------------------
Receive2(p, q) ==
    /\ pc[p] = "wait2"
    /\ \E m \in msgs :
          /\ m.type = "ph2"
          /\ m.sender = q
          /\ (* record the estimated value received from q *)
             estReceived' = [estReceived EXCEPT ![p][m.est] = @ \cup {q}]
    /\ UNCHANGED <<pc, view, prop, est, dec, msgs>>

Decide(p, e) ==
    /\ pc[p] = "wait2"
    /\ e \in Values
    /\ Cardinality(estReceived[p][e]) >= N - T
    /\ dec' = [dec EXCEPT ![p] = e]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, msgs, estReceived>>

GoToChoosing(p) ==
    /\ pc[p] = "wait2"
    /\ Cardinality({ q \in Proc :
          \E m \in msgs : m.type = "ph2" /\ m.sender = q }) = N
    /\ \A e \in Values : Cardinality(estReceived[p][e]) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, prop, est, dec, msgs, estReceived>>

Choose(p) ==
    /\ pc[p] = "choosing"
    /\ LET vals == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
         vals # {}
    /\ dec' = [dec EXCEPT ![p] = Max(vals)]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, msgs, estReceived>>

\* ----------------------------------------------------------------------
\* Crash action
\* ----------------------------------------------------------------------
Crash(p) ==
    /\ pc[p] # "crashed"
    /\ Cardinality({ q \in Proc : pc[q] = "crashed" }) < F
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<view, prop, est, dec, msgs, estReceived>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : Bcast1(p)
    \/ \E p \in Proc : Phase1Complete(p)
    \/ \E p \in Proc : Bcast2(p)
    \/ \E p \in Proc, q \in Proc : Receive1(p, q)
    \/ \E p \in Proc, q \in Proc : Receive2(p, q)
    \/ \E p \in Proc, e \in Values : Decide(p, e)
    \/ \E p \in Proc : GoToChoosing(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> {"bcast1","wait1","bcast2","wait2","done","crashed","choosing"}]
    /\ view \in [Proc -> [Proc -> Values]]
    /\ \A p,q : view[p][q] = Bottom \/ view[p][q] \in Values
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> Values]
    /\ dec \in [Proc -> Values]
    /\ msgs \subseteq Message
    /\ estReceived \in [Proc -> [Values -> SUBSET Proc]]
    /\ Bottom \notin Values

Validity ==
    \A p \in Proc :
        dec[p] # Bottom => \E q \in Proc : prop[q] = dec[p]

Agreement ==
    \A p,q \in Proc :
        (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

====