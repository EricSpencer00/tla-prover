---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Types and basic sets
\* ----------------------------------------------------------------------
Proc == 1..N

Message ==
  [type : {"P1","P2"},
   sender : Proc,
   value  : Values,
   est    : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc, view, prop, est, dec, crashed, sent, recv

vars == << pc, view, prop, est, dec, crashed, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Maximum of a non‑empty set (Values are totally ordered, assumed to be Nat)
Max(S) == 
  IF S = {} THEN Bottom
  ELSE CHOOSE x \in S : \A y \in S : y <= x

ReceivedSenders(p) == { m.sender : m \in recv[p] /\ m.type = "P1" }

ReceivedEstimates(p) == { m.est : m \in recv[p] /\ m.type = "P2" }

CountEst(v,p) == 
  Cardinality({ m \in recv[p] : m.type = "P2" /\ m.est = v })

AllP2Senders(p) == 
  { m.sender : m \in recv[p] /\ m.type = "P2" }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Proc |-> "b1"]
  /\ prop = [p \in Proc |-> CHOOSE v \in Values : TRUE]   \* nondet proposal
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ crashed = {}
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
  /\ pc[p] = "b1"
  /\ pc' = [pc EXCEPT ![p] = "w1"]
  /\ sent' = sent \cup { [type |-> "P1", sender |-> p,
                         value |-> prop[p],
                         est   |-> Bottom] }
  /\ UNCHANGED << view, prop, est, dec, crashed, recv >>

Receive1(p, m) ==
  /\ pc[p] = "w1"
  /\ m \in sent
  /\ m.type = "P1"
  /\ m.sender \notin crashed
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << pc, prop, est, dec, crashed, sent >>

Phase1to2(p) ==
  /\ pc[p] = "w1"
  /\ Cardinality(ReceivedSenders(p)) >= N - T
  /\ est' = [est EXCEPT ![p] = Max({ view[p][q] : q \in Proc })]
  /\ pc' = [pc EXCEPT ![p] = "b2"]
  /\ UNCHANGED << view, prop, dec, crashed, sent, recv >>

Broadcast2(p) ==
  /\ pc[p] = "b2"
  /\ pc' = [pc EXCEPT ![p] = "w2"]
  /\ sent' = sent \cup { [type |-> "P2", sender |-> p,
                         value |-> prop[p],
                         est   |-> est[p]] }
  /\ UNCHANGED << view, prop, est, dec, crashed, recv >>

Receive2(p, m) ==
  /\ pc[p] = "w2"
  /\ m \in sent
  /\ m.type = "P2"
  /\ m.sender \notin crashed
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << pc, view, prop, est, dec, crashed, sent >>

Decide(p) ==
  /\ pc[p] = "w2"
  /\ \E v \in Values :
        CountEst(v,p) >= N - T
  /\ LET v == CHOOSE w \in Values : CountEst(w,p) >= N - T IN
        /\ dec' = [dec EXCEPT ![p] = v]
        /\ pc'  = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashed, sent, recv >>

MoveToChoose(p) ==
  /\ pc[p] = "w2"
  /\ AllP2Senders(p) = Proc
  /\ \A v \in Values : CountEst(v,p) < N - T
  /\ LET candidates == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
        /\ candidates # {}
        /\ choice == CHOOSE x \in candidates : TRUE
        /\ dec' = [dec EXCEPT ![p] = choice]
        /\ pc'  = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashed, sent, recv >>

ChooseDeterministic(p) ==
  /\ pc[p] = "choose"
  /\ LET candidates == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
        /\ candidates # {}
        /\ choice == CHOOSE x \in candidates : TRUE
        /\ dec' = [dec EXCEPT ![p] = choice]
        /\ pc'  = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashed, sent, recv >>

Crash(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ Cardinality(crashed) < F
  /\ crashed' = crashed \cup {p}
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED << view, prop, est, dec, sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Proc : Broadcast1(p)
  \/ \E p \in Proc, m \in Message : Receive1(p,m)
  \/ \E p \in Proc : Phase1to2(p)
  \/ \E p \in Proc : Broadcast2(p)
  \/ \E p \in Proc, m \in Message : Receive2(p,m)
  \/ \E p \in Proc : Decide(p)
  \/ \E p \in Proc : MoveToChoose(p)
  \/ \E p \in Proc : ChooseDeterministic(p)
  \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> {"b1","w1","b2","w2","done","crashed","choose"}]
  /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> (Values \cup {Bottom})]
  /\ dec \in [Proc -> (Values \cup {Bottom})]
  /\ crashed \subseteq Proc
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Proc :
    dec[p] # Bottom => 
      (\E q \in Proc : prop[q] = dec[p])

Agreement ==
  \A p,q \in Proc :
    (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* The required identifiers
\* ----------------------------------------------------------------------
SPECIFICATION == Spec
INVARIANTS == TypeOK, Validity, Agreement

====