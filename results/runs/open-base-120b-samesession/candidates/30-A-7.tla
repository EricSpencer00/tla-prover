---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Process == 1..N

PcStates == {"bcast1", "wait1", "bcast2", "wait2", "choosing", "done", "crashed"}

Msg == [type : {"phase1","phase2"},
        sender : Process,
        value  : Values,      \* for phase1
        prop   : Values,      \* for phase2 (proposed value)
        est    : Values]      \* for phase2 (estimated value)

Phase1Msg(m) == m.type = "phase1"
Phase2Msg(m) == m.type = "phase2"

\* Maximum of a non‑empty set of values (Values is totally ordered)
Max(S) ==
  IF S = {} THEN Bottom
  ELSE
    CHOOSE x \in S :
      \A y \in S : y <= x

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc, view, prop, est, dec, crashed, sent, recv

\* pc[p]      : control location of process p
\* view[p][q] : value learned from p about q (initially Bottom)
\* prop[p]    : proposed value of p
\* est[p]     : estimated value after phase‑1 (initially Bottom)
\* dec[p]     : decision value of p (Bottom means undecided)
\* crashed    : set of crashed processes
\* sent       : set of messages that have been broadcast
\* recv[p]    : set of messages that p has already received

vars == << pc, view, prop, est, dec, crashed, sent, recv >>

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Process |-> "bcast1"]
  /\ view = [p \in Process |-> [q \in Process |-> Bottom]]
  /\ prop \in [p \in Process |-> Values]
  /\ est = [p \in Process |-> Bottom]
  /\ dec = [p \in Process |-> Bottom]
  /\ crashed = {}
  /\ sent = {}
  /\ recv = [p \in Process |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* --- Broadcast phase‑1 --------------------------------------------------
Broadcast1(p) ==
  /\ p \in Process
  /\ pc[p] = "bcast1"
  /\ pc' = [pc EXCEPT ![p] = "wait1"]
  /\ sent' = sent \cup {
        [type |-> "phase1",
         sender |-> p,
         value |-> prop[p],
         prop |-> Bottom,    \* unused for phase1
         est |-> Bottom] }
  /\ UNCHANGED << view, prop, est, dec, crashed, recv >>

\* --- Receive a phase‑1 message -----------------------------------------
Receive1(p, m) ==
  /\ p \in Process
  /\ pc[p] = "wait1"
  /\ m \in sent
  /\ Phase1Msg(m)
  /\ m.sender \notin crashed
  /\ m \notin recv[p]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ UNCHANGED << pc, prop, est, dec, crashed, sent >>

\* --- Transition after enough phase‑1 messages -------------------------
Phase1Ready(p) ==
  LET senders == { m.sender : m \in recv[p] /\ Phase1Msg(m) } IN
  /\ pc[p] = "wait1"
  /\ Cardinality(senders) >= N - T
  /\ est' = [est EXCEPT ![p] = Max({ view[p][q] : q \in Process })]
  /\ pc' = [pc EXCEPT ![p] = "bcast2"]
  /\ UNCHANGED << view, prop, dec, crashed, sent, recv >>

\* --- Broadcast phase‑2 -------------------------------------------------
Broadcast2(p) ==
  /\ p \in Process
  /\ pc[p] = "bcast2"
  /\ pc' = [pc EXCEPT ![p] = "wait2"]
  /\ sent' = sent \cup {
        [type |-> "phase2",
         sender |-> p,
         value |-> Bottom,    \* unused for phase2
         prop |-> prop[p],
         est  |-> est[p]] }
  /\ UNCHANGED << view, prop, est, dec, crashed, recv >>

\* --- Receive a phase‑2 message -----------------------------------------
Receive2(p, m) ==
  /\ p \in Process
  /\ pc[p] = "wait2"
  /\ m \in sent
  /\ Phase2Msg(m)
  /\ m.sender \notin crashed
  /\ m \notin recv[p]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << pc, view, prop, est, dec, crashed, sent >>

\* --- Decide when N‑T equal estimated values have been seen -------------
DecideFromEst(p) ==
  /\ p \in Process
  /\ pc[p] = "wait2"
  /\ \E v \in Values :
        Cardinality({ m \in recv[p] : Phase2Msg(m) /\ m.est = v }) >= N - T
  LET v == CHOOSE w \in Values :
                Cardinality({ m \in recv[p] : Phase2Msg(m) /\ m.est = w }) >= N - T
  IN
  /\ dec' = [dec EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashed, sent, recv >>

\* --- Move to choosing when all phase‑2 messages received ---------------
MoveToChoosing(p) ==
  /\ p \in Process
  /\ pc[p] = "wait2"
  /\ { m.sender : m \in recv[p] /\ Phase2Msg(m) } = Process
  /\ \A v \in Values :
        Cardinality({ m \in recv[p] : Phase2Msg(m) /\ m.est = v }) < N - T
  /\ pc' = [pc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED << view, prop, est, dec, crashed, sent, recv >>

\* --- Choose deterministically from local view -------------------------
ChooseAndDecide(p) ==
  /\ p \in Process
  /\ pc[p] = "choosing"
  /\ LET candidates == { view[p][q] : q \in Process /\ view[p][q] # Bottom } IN
     candidates # {}
  LET v == Max(candidates) IN
  /\ dec' = [dec EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashed, sent, recv >>

\* --- Crash a process --------------------------------------------------
Crash(p) ==
  /\ p \in Process
  /\ p \notin crashed
  /\ Cardinality(crashed) < F
  /\ crashed' = crashed \cup {p}
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED << view, prop, est, dec, sent, recv >>

\* ----------------------------------------------------------------------
\* Next relation (disjunction of all possible actions)
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Process : Broadcast1(p)
  \/ \E p \in Process, m \in sent : Receive1(p, m)
  \/ \E p \in Process : Phase1Ready(p)
  \/ \E p \in Process : Broadcast2(p)
  \/ \E p \in Process, m \in sent : Receive2(p, m)
  \/ \E p \in Process : DecideFromEst(p)
  \/ \E p \in Process : MoveToChoosing(p)
  \/ \E p \in Process : ChooseAndDecide(p)
  \/ \E p \in Process : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Process -> PcStates]
  /\ view \in [Process -> [Process -> Values \cup {Bottom}]]
  /\ prop \in [Process -> Values]
  /\ est \in [Process -> Values \cup {Bottom}]
  /\ dec \in [Process -> Values \cup {Bottom}]
  /\ crashed \subseteq Process
  /\ sent \subseteq Msg
  /\ recv \in [Process -> SUBSET Msg]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Process :
    dec[p] # Bottom =>
      (\E q \in Process : prop[q] = dec[p])

Agreement ==
  \A p, q \in Process :
    (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* The set of invariants required by the cfg file
\* ----------------------------------------------------------------------
INVARIANTS == TypeOK \* also exported individually
\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====