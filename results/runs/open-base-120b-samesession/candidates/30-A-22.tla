---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Process locations (control states)
\* ----------------------------------------------------------------------
Phase1Broadcast == "Phase1Broadcast"
Phase1Wait       == "Phase1Wait"
Phase2Broadcast == "Phase2Broadcast"
Phase2Wait      == "Phase2Wait"
Choosing        == "Choosing"
Done            == "Done"
Crashed         == "Crashed"

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES loc, view, prop, est, dec, crashedCount, sent, recv

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of process identifiers
Proc == 1..N

\* A message record
Message == [type : {"p1","p2"}, value : Values, sender : Proc,
            est : Values \cup {Bottom}]

\* Maximum element of a non‑empty set of Values (Values are totally ordered,
\* e.g. natural numbers).  If the set is empty the result is Bottom.
MaxValue(V) ==
  IF V = {} THEN Bottom
  ELSE CHOOSE v \in V : \A w \in V : w <= v

\* The set of senders from which process i has received a phase‑1 message
Senders1(i) == { m.sender : m \in recv[i] /\ m.type = "p1" }

\* The set of senders from which process i has received a phase‑2 message
Senders2(i) == { m.sender : m \in recv[i] /\ m.type = "p2" }

\* The multiset of estimated values received in phase‑2 by i
EstVals2(i) == { m.est : m \in recv[i] /\ m.type = "p2" }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ loc = [i \in Proc |-> Phase1Broadcast]
  /\ view = [i \in Proc, j \in Proc |-> Bottom]
  /\ prop \in [Proc -> Values]
  /\ est = [i \in Proc |-> Bottom]
  /\ dec = [i \in Proc |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [i \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(i) ==
  /\ loc[i] = Phase1Broadcast
  /\ loc' = [loc EXCEPT ![i] = Phase1Wait]
  /\ sent' = sent \cup { [type |-> "p1",
                         value |-> prop[i],
                         sender |-> i,
                         est |-> Bottom] }
  /\ UNCHANGED << view, prop, est, dec, crashedCount, recv >>

Broadcast2(i) ==
  /\ loc[i] = Phase2Broadcast
  /\ loc' = [loc EXCEPT ![i] = Phase2Wait]
  /\ sent' = sent \cup { [type |-> "p2",
                         value |-> prop[i],
                         sender |-> i,
                         est |-> est[i]] }
  /\ UNCHANGED << view, prop, est, dec, crashedCount, recv >>

Receive1(i) ==
  /\ \E m \in sent :
        /\ m.type = "p1"
        /\ m \notin recv[i]
        /\ loc[i] = Phase1Wait
  /\ LET m == CHOOSE mm \in sent :
                    mm.type = "p1" /\ mm \notin recv[i] /\ loc[i] = Phase1Wait
      IN
        /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
        /\ view' = [view EXCEPT ![i][m.sender] = m.value]
  /\ UNCHANGED << loc, prop, est, dec, crashedCount, sent >>

Receive2(i) ==
  /\ \E m \in sent :
        /\ m.type = "p2"
        /\ m \notin recv[i]
        /\ loc[i] = Phase2Wait
  /\ LET m == CHOOSE mm \in sent :
                    mm.type = "p2" /\ mm \notin recv[i] /\ loc[i] = Phase2Wait
      IN
        /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
        /\ view' = [view EXCEPT ![i][m.sender] = m.value]
  /\ UNCHANGED << loc, prop, est, dec, crashedCount, sent >>

ComputeEst(i) ==
  /\ loc[i] = Phase1Wait
  /\ Cardinality(Senders1(i)) >= N - T
  /\ est' = [est EXCEPT ![i] = MaxValue({ view[i][j] : j \in Proc })]
  /\ loc' = [loc EXCEPT ![i] = Phase2Broadcast]
  /\ UNCHANGED << view, prop, dec, crashedCount, sent, recv >>

Decide(i) ==
  /\ loc[i] = Phase2Wait
  /\ \E v \in Values :
        Cardinality({ m.sender : m \in recv[i] /\ m.type = "p2" /\ m.est = v }) >= N - T
  /\ LET v == CHOOSE vv \in Values :
                 Cardinality({ m.sender : m \in recv[i] /\ m.type = "p2" /\ m.est = vv }) >= N - T
      IN
        /\ dec' = [dec EXCEPT ![i] = v]
        /\ loc' = [loc EXCEPT ![i] = Done]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

MoveToChoosing(i) ==
  /\ loc[i] = Phase2Wait
  /\ Cardinality(Senders2(i)) = N            \* received from all senders
  /\ \A v \in Values :
        Cardinality({ m.sender : m \in recv[i] /\ m.type = "p2" /\ m.est = v }) < N - T
  /\ loc' = [loc EXCEPT ![i] = Choosing]
  /\ UNCHANGED << view, prop, est, dec, crashedCount, sent, recv >>

Choose(i) ==
  /\ loc[i] = Choosing
  /\ \E v \in Values :
        v \in { view[i][j] : j \in Proc }
  /\ LET v == CHOOSE vv \in Values :
                 vv \in { view[i][j] : j \in Proc }
      IN
        /\ dec' = [dec EXCEPT ![i] = v]
        /\ loc' = [loc EXCEPT ![i] = Done]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

Crash(i) ==
  /\ crashedCount < F
  /\ loc[i] # Crashed
  /\ loc[i] # Done
  /\ loc' = [loc EXCEPT ![i] = Crashed]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << view, prop, est, dec, sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E i \in Proc :
        \/ Broadcast1(i)
        \/ Broadcast2(i)
        \/ Receive1(i)
        \/ Receive2(i)
        \/ ComputeEst(i)
        \/ Decide(i)
        \/ MoveToChoosing(i)
        \/ Choose(i)
        \/ Crash(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< loc, view, prop, est, dec, crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ loc \in [Proc -> {"Phase1Broadcast","Phase1Wait","Phase2Broadcast",
                      "Phase2Wait","Choosing","Done","Crashed"}]
  /\ view \in [Proc -> [Proc -> Values \cup {Bottom}]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> Values \cup {Bottom}]
  /\ dec \in [Proc -> Values \cup {Bottom}]
  /\ crashedCount \in Nat
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
  \A i \in Proc :
    dec[i] # Bottom => dec[i] \in Values /\ \E j \in Proc : prop[j] = dec[i]

Agreement ==
  \A i, j \in Proc :
    /\ dec[i] # Bottom
    /\ dec[j] # Bottom
    => dec[i] = dec[j]

====