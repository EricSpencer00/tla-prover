---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived sets and types
\* ----------------------------------------------------------------------
Proc == 1..N
ValueSet == Values \cup {Bottom}

Message == [type : {"ph1", "ph2"},
            sender : Proc,
            value  : ValueSet,
            est    : ValueSet]   \* for phase‑1 messages est = Bottom

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc, view, prop, est, dec, msgs, recv, crashedCount

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
MaxInSet(S) == 
  IF S = {} THEN Bottom 
  ELSE CHOOSE v \in S : \A w \in S : v >= w

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Proc |-> "b1"]                         \* broadcast phase‑1
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ prop \in [Proc -> Values]                         \* each process proposes a value
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ msgs = {}                                          \* no messages yet
  /\ recv = [p \in Proc |-> {}]
  /\ crashedCount = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Broadcast a phase‑1 message
Broadcast1(p) ==
  /\ pc[p] = "b1"
  /\ LET m == [type |-> "ph1",
               sender |-> p,
               value |-> prop[p],
               est   |-> Bottom] IN
     msgs' = msgs \cup {m}
  /\ pc' = [pc EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<view, prop, est, dec, recv, crashedCount>>

\* Receive a phase‑1 message
Receive1(p, m) ==
  /\ pc[p] = "w1"
  /\ m \in msgs
  /\ m.type = "ph1"
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<pc, prop, est, dec, msgs, crashedCount>>

\* After enough phase‑1 messages, compute estimate and move to phase‑2 broadcast
ToBroadcast2(p) ==
  /\ pc[p] = "w1"
  /\ Cardinality({s \in Proc : view[p][s] # Bottom}) >= N - T
  /\ est' = [est EXCEPT ![p] = MaxInSet({view[p][s] : s \in Proc})]
  /\ pc' = [pc EXCEPT ![p] = "b2"]
  /\ UNCHANGED <<view, prop, dec, msgs, recv, crashedCount>>

\* Broadcast a phase‑2 message
Broadcast2(p) ==
  /\ pc[p] = "b2"
  /\ LET m == [type |-> "ph2",
               sender |-> p,
               value |-> prop[p],
               est   |-> est[p]] IN
     msgs' = msgs \cup {m}
  /\ pc' = [pc EXCEPT ![p] = "w2"]
  /\ UNCHANGED <<view, prop, est, dec, recv, crashedCount>>

\* Receive a phase‑2 message
Receive2(p, m) ==
  /\ pc[p] = "w2"
  /\ m \in msgs
  /\ m.type = "ph2"
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<pc, view, prop, est, dec, msgs, crashedCount>>

\* Decide when at least N‑T equal estimates have been seen
Decide(p, v) ==
  /\ pc[p] = "w2"
  /\ v \in Values
  /\ Cardinality({m \in recv[p] : m.type = "ph2" /\ m.est = v}) >= N - T
  /\ dec' = [dec EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, msgs, recv, crashedCount>>

\* Move to choosing state when all N phase‑2 messages received but no majority
ToChoosing(p) ==
  /\ pc[p] = "w2"
  /\ Cardinality({m \in recv[p] : m.type = "ph2"}) = N
  /\ \A v \in Values :
        Cardinality({m \in recv[p] : m.type = "ph2" /\ m.est = v}) < N - T
  /\ pc' = [pc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, prop, est, dec, msgs, recv, crashedCount>>

\* Choose a value that appears in the local view and decide
Choose(p) ==
  /\ pc[p] = "choosing"
  /\ LET candidates == {view[p][s] : s \in Proc /\ view[p][s] # Bottom} IN
       candidates # {}
  /\ dec' = [dec EXCEPT ![p] = CHOOSE v \in candidates : TRUE]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, msgs, recv, crashedCount>>

\* Crash a process (if fewer than F have crashed so far)
Crash(p) ==
  /\ crashedCount < F
  /\ pc[p] # "crashed"
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, prop, est, dec, msgs, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation (disjunction of all possible actions)
\* ----------------------------------------------------------------------
Next ==
  \E p \in Proc :
    \/ Broadcast1(p)
    \/ \E m \in Message :
         (Receive1(p, m) \/ Receive2(p, m))
    \/ ToBroadcast2(p)
    \/ Broadcast2(p)
    \/ \E v \in Values : Decide(p, v)
    \/ ToChoosing(p)
    \/ Choose(p)
    \/ Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, view, prop, est, dec, msgs, recv, crashedCount>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> {"b1","w1","b2","w2","choosing","done","crashed"}]
  /\ view \in [Proc -> [Proc -> ValueSet]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> ValueSet]
  /\ dec \in [Proc -> ValueSet]
  /\ msgs \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]
  /\ crashedCount \in Nat
  /\ crashedCount <= F

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Proc :
    IF dec[p] # Bottom
    THEN /\ dec[p] \in Values
         /\ \E q \in Proc : dec[p] = prop[q]
    ELSE TRUE

Agreement ==
  \A p, q \in Proc :
    (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* The set of invariants required by the configuration file
\* ----------------------------------------------------------------------
INVARIANT TypeOK
INVARIANT Validity
INVARIANT Agreement

====