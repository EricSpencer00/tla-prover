---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* -----------------------------------------------------------------
\* Basic definitions
\* -----------------------------------------------------------------
Proc   == 1..N
LocSet == {"bcast1", "wait1", "bcast2", "wait2", "choosing", "done", "crashed"}

Message == 
    [type : "phase1",  sender : Proc, v : Values] 
  \cup 
    [type : "phase2",  sender : Proc, v : Values, est : Values]

\* -----------------------------------------------------------------
\* State variables
\* -----------------------------------------------------------------
VARIABLES 
    loc,        \* [p \in Proc |-> LocSet]
    view,       \* [p \in Proc |-> [q \in Proc |-> Values \cup {Bottom}]]
    prop,       \* [p \in Proc |-> Values]
    est,        \* [p \in Proc |-> Values \cup {Bottom}]
    dec,        \* [p \in Proc |-> Values \cup {Bottom}]
    crashed,    \* SUBSET Proc
    sent,       \* SUBSET Message
    recv        \* [p \in Proc |-> SUBSET Message]

vars == << loc, view, prop, est, dec, crashed, sent, recv >>

\* -----------------------------------------------------------------
\* Helper operators
\* -----------------------------------------------------------------
Max(S) == 
    IF S = {} THEN Bottom
    ELSE CHOOSE x \in S : \A y \in S : y <= x

\* -----------------------------------------------------------------
\* Type correctness invariant
\* -----------------------------------------------------------------
TypeOK ==
    /\ loc \in [Proc -> LocSet]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ dec \in [Proc -> (Values \cup {Bottom})]
    /\ crashed \subseteq Proc
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

\* -----------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------
Init ==
    /\ loc = [p \in Proc |-> "bcast1"]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ prop \in [Proc -> Values]          \* arbitrary initial proposals
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* -----------------------------------------------------------------
\* Actions
\* -----------------------------------------------------------------
\* Broadcast phase‑1
Broadcast1(p) ==
    /\ loc[p] = "bcast1"
    /\ UNCHANGED << view, est, dec, crashed, recv >>
    /\ let m == [type |-> "phase1", sender |-> p, v |-> prop[p]] in
       /\ sent' = sent \cup {m}
    /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED << prop >>

\* Receive a phase‑1 message
Receive1(p, m) ==
    /\ m \in sent
    /\ m.type = "phase1"
    /\ loc[p] = "wait1"
    /\ UNCHANGED << prop, est, dec, crashed, sent >>
    /\ view' = [view EXCEPT ![p][m.sender] = m.v]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ loc' = loc

\* Transition after enough phase‑1 messages: compute estimate and broadcast phase‑2
Phase1Done(p) ==
    /\ loc[p] = "wait1"
    /\ LET receivedSenders == { s \in Proc : view[p][s] # Bottom } IN
       Cardinality(receivedSenders) >= N - T
    /\ LET maxVal == Max({ view[p][s] : s \in Proc }) IN
       /\ est' = [est EXCEPT ![p] = maxVal]
    /\ UNCHANGED << prop, view, dec, crashed, sent, recv >>
    /\ let m == [type |-> "phase2", sender |-> p, v |-> prop[p], est |-> maxVal] in
       sent' = sent \cup {m}
    /\ loc' = [loc EXCEPT ![p] = "wait2"]

\* Receive a phase‑2 message
Receive2(p, m) ==
    /\ m \in sent
    /\ m.type = "phase2"
    /\ loc[p] = "wait2"
    /\ UNCHANGED << prop, est, dec, crashed, sent, loc >>
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ view' = view   \* view of proposals unchanged; we keep it for choosing

\* Decision when enough identical estimates are seen
DecideFromEst(p) ==
    /\ loc[p] = "wait2"
    /\ \E v \in Values :
          Cardinality({ s \in Proc : 
                \E m \in recv[p] : m.type = "phase2" /\ m.sender = s /\ m.est = v }) >= N - T
    /\ LET chosen == CHOOSE v \in Values :
          Cardinality({ s \in Proc : 
                \E m \in recv[p] : m.type = "phase2" /\ m.sender = s /\ m.est = v }) >= N - T
       IN
          /\ dec' = [dec EXCEPT ![p] = chosen]
          /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED << prop, view, est, crashed, sent, recv >>

\* Move to choosing when all phase‑2 messages received but no majority estimate
MoveToChoosing(p) ==
    /\ loc[p] = "wait2"
    /\ Cardinality({ s \in Proc : \E m \in recv[p] : m.type = "phase2" /\ m.sender = s }) = N
    /\ \A v \in Values :
          Cardinality({ s \in Proc : 
                \E m \in recv[p] : m.type = "phase2" /\ m.sender = s /\ m.est = v }) < N - T
    /\ UNCHANGED << prop, view, est, dec, crashed, sent, recv >>
    /\ loc' = [loc EXCEPT ![p] = "choosing"]

\* Choosing a value deterministically from the local view
ChooseAndDecide(p) ==
    /\ loc[p] = "choosing"
    /\ LET candidates == { view[p][s] : s \in Proc /\ view[p][s] # Bottom } IN
       candidates # {}
    /\ LET chosen == CHOOSE v \in candidates : TRUE IN
          /\ dec' = [dec EXCEPT ![p] = chosen]
          /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED << prop, view, est, crashed, sent, recv >>

\* Crash a process (as long as fewer than F have crashed)
Crash(p) ==
    /\ p \notin crashed
    /\ Cardinality(crashed) < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED << view, prop, est, dec, sent, recv >>

\* -----------------------------------------------------------------
\* Next-state relation
\* -----------------------------------------------------------------
Next ==
    \E p \in Proc :
        \/ Broadcast1(p)
        \/ \E m \in Message : Receive1(p, m)
        \/ Phase1Done(p)
        \/ \E m \in Message : Receive2(p, m)
        \/ DecideFromEst(p)
        \/ MoveToChoosing(p)
        \/ ChooseAndDecide(p)
        \/ Crash(p)

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* -----------------------------------------------------------------
\* Safety invariants
\* -----------------------------------------------------------------
Validity ==
    \A p \in Proc :
        dec[p] # Bottom => 
            \E q \in Proc : prop[q] = dec[p]

Agreement ==
    \A p, q \in Proc :
        /\ dec[p] # Bottom
        /\ dec[q] # Bottom
        => dec[p] = dec[q]

\* -----------------------------------------------------------------
\* Assumptions
\* -----------------------------------------------------------------
ASSUME /\ 2 * T < N
       /\ 0 <= F /\ F <= T
       /\ N > 0
       /\ Bottom \notin Values

====