---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Basic definitions
\* ----------------------------------------------------------------------
Proc == 1..N

Msg == [type : {"phase1", "phase2"},
        sender : Proc,
        v : Values,
        e : Values]   \* For phase1 messages e = Bottom

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc, view, prop, est, dec, msgs, recv

vars == << pc, view, prop, est, dec, msgs, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Set of values that have been proposed (used for validity)
ProposedVals == { prop[p] : p \in Proc }

\* The set of distinct senders from which a process p has received phase‑1 messages
Senders1(p) == { m.sender : m \in recv[p] /\ m.type = "phase1" }

\* The set of distinct senders from which a process p has received phase‑2 messages
Senders2(p) == { m.sender : m \in recv[p] /\ m.type = "phase2" }

\* The multiset of estimated values received in phase‑2
EstVals(p) == { m.e : m \in recv[p] /\ m.type = "phase2" }

\* Number of processes that have crashed
CrashedCount == Cardinality({ p \in Proc : pc[p] = "crash" })

\* Maximum of a non‑empty set of values (Values are assumed to be numbers)
MaxVal(S) == IF S = {} THEN Bottom
            ELSE CHOOSE x \in S : \A y \in S : y <= x

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "b1"]                     \* broadcast phase‑1
    /\ prop \in [Proc -> Values]                     \* each process proposes a value
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ msgs = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Broadcast phase‑1
Broadcast1(p) ==
    /\ pc[p] = "b1"
    /\ UNCHANGED << view, est, dec, recv >>
    /\ msgs' = msgs \cup { [type |-> "phase1",
                           sender |-> p,
                           v |-> prop[p],
                           e |-> Bottom] }
    /\ pc' = [pc EXCEPT ![p] = "w1"]
    /\ UNCHANGED << prop >>

\* 2. Receive a phase‑1 message
Receive1(p, m) ==
    /\ pc[p] = "w1"
    /\ m \in msgs
    /\ m.type = "phase1"
    /\ view' = [view EXCEPT ![p][m.sender] = m.v]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << pc, prop, est, dec, msgs >>

\* 3. After having N‑T distinct phase‑1 messages, compute estimate and go to phase‑2 broadcast
Estimate(p) ==
    /\ pc[p] = "w1"
    /\ Cardinality(Senders1(p)) >= N - T
    /\ LET vals == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
       est' = [est EXCEPT ![p] = MaxVal(vals)]
    /\ pc' = [pc EXCEPT ![p] = "b2"]
    /\ UNCHANGED << view, prop, dec, msgs, recv >>

\* 4. Broadcast phase‑2
Broadcast2(p) ==
    /\ pc[p] = "b2"
    /\ msgs' = msgs \cup { [type |-> "phase2",
                           sender |-> p,
                           v |-> prop[p],
                           e |-> est[p]] }
    /\ pc' = [pc EXCEPT ![p] = "w2"]
    /\ UNCHANGED << view, prop, est, dec, recv >>

\* 5. Receive a phase‑2 message
Receive2(p, m) ==
    /\ pc[p] = "w2"
    /\ m \in msgs
    /\ m.type = "phase2"
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << pc, view, prop, est, dec, msgs >>

\* 6. Decide when N‑T equal estimated values have been seen
DecideByThreshold(p) ==
    /\ pc[p] = "w2"
    /\ \E ev \in Values :
         Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.e = ev }) >= N - T
    /\ LET ev == CHOOSE v \in Values :
                Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.e = v }) >= N - T
       IN
       dec' = [dec EXCEPT ![p] = ev]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, msgs, recv >>

\* 7. If all N phase‑2 messages have been received without a threshold, move to choosing
AllPhase2Received(p) ==
    /\ pc[p] = "w2"
    /\ Cardinality(Senders2(p)) = N
    /\ pc' = [pc EXCEPT ![p] = "choose"]
    /\ UNCHANGED << view, prop, est, dec, msgs, recv >>

\* 8. Choose a value that appears in the local view and decide
Choose(p) ==
    /\ pc[p] = "choose"
    /\ LET seenVals == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
       \E v \in seenVals :
          dec' = [dec EXCEPT ![p] = v] /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, msgs, recv >>

\* 9. Crash a process (up to F crashes)
Crash(p) ==
    /\ pc[p] # "crash"
    /\ pc[p] # "done"
    /\ CrashedCount < F
    /\ pc' = [pc EXCEPT ![p] = "crash"]
    /\ UNCHANGED << view, prop, est, dec, msgs, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : Broadcast1(p)
    \/ \E p \in Proc, m \in msgs : Receive1(p, m)
    \/ \E p \in Proc : Estimate(p)
    \/ \E p \in Proc : Broadcast2(p)
    \/ \E p \in Proc, m \in msgs : Receive2(p, m)
    \/ \E p \in Proc : DecideByThreshold(p)
    \/ \E p \in Proc : AllPhase2Received(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> {"b1","w1","b2","w2","done","crash","choose"}]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ dec \in [Proc -> (Values \cup {Bottom})]
    /\ msgs \subseteq Msg
    /\ recv \in [Proc -> SUBSET Msg]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        dec[p] # Bottom => dec[p] \in ProposedVals

Agreement ==
    \A p, q \in Proc :
        (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* Assumptions on the constants
\* ----------------------------------------------------------------------
ASSUME 0 < N
ASSUME 2 * T < N
ASSUME 0 <= F /\ F <= T
ASSUME Bottom \notin Values

====