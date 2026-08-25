---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Basic definitions
\* ----------------------------------------------------------------------
Proc == 1 .. N

Message == [type : {"p1", "p2"},
            val  : Values,
            sender : Proc,
            est  : Values \cup {Bottom}]

IsP1(m) == m.type = "p1"
IsP2(m) == m.type = "p2"

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES loc, view, prop, est, decision,
          crashed, crashCount,
          sent, recv

vars == << loc, view, prop, est, decision,
           crashed, crashCount,
           sent, recv >>

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
Max(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE x \in S : \A y \in S : y <= x

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
/\ loc = [p \in Proc |-> "bcast1"]
/\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
/\ prop \in [p \in Proc -> Values]
/\ est = [p \in Proc |-> Bottom]
/\ decision = [p \in Proc |-> Bottom]
/\ crashed = {}
/\ crashCount = 0
/\ sent = {}
/\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
  /\ loc[p] = "bcast1"
  /\ let m == [type |-> "p1",
               val  |-> prop[p],
               sender |-> p,
               est  |-> Bottom] in
     /\ sent' = sent \cup {m}
     /\ loc' = [loc EXCEPT ![p] = "wait1"]
     /\ UNCHANGED << view, prop, est, decision,
                     crashed, crashCount, recv >>

Receive1(p, m) ==
  /\ loc[p] = "wait1"
  /\ IsP1(m)
  /\ m \in sent
  /\ ~(m \in recv[p])
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << loc, prop, est, decision,
                 crashed, crashCount, sent >>

Transition1(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality({ s \in Proc : \E m \in recv[p] :
                     IsP1(m) /\ m.sender = s }) >= N - T
  /\ let estVal == Max({ view[p][q] : q \in Proc }) in
       /\ est' = [est EXCEPT ![p] = estVal]
       /\ loc' = [loc EXCEPT ![p] = "bcast2"]
  /\ UNCHANGED << view, prop, decision,
                 crashed, crashCount, sent, recv >>

Broadcast2(p) ==
  /\ loc[p] = "bcast2"
  /\ let m == [type |-> "p2",
               val  |-> prop[p],
               sender |-> p,
               est  |-> est[p]] in
     /\ sent' = sent \cup {m}
     /\ loc' = [loc EXCEPT ![p] = "wait2"]
     /\ UNCHANGED << view, prop, est, decision,
                     crashed, crashCount, recv >>

Receive2(p, m) ==
  /\ loc[p] = "wait2"
  /\ IsP2(m)
  /\ m \in sent
  /\ ~(m \in recv[p])
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << loc, prop, est, decision,
                 crashed, crashCount, sent >>

Decide(p, v) ==
  /\ loc[p] = "wait2"
  /\ v \in Values
  /\ Cardinality({ m \in recv[p] : IsP2(m) /\ m.est = v }) >= N - T
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est,
                 crashed, crashCount, sent, recv >>

MoveToChoosing(p) ==
  /\ loc[p] = "wait2"
  /\ Cardinality({ m \in recv[p] : IsP2(m) }) = N
  /\ \A v \in Values :
        Cardinality({ m \in recv[p] : IsP2(m) /\ m.est = v }) < N - T
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED << view, prop, est, decision,
                 crashed, crashCount, sent, recv >>

Choose(p) ==
  /\ loc[p] = "choosing"
  /\ LET candidates == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
       candidates # {}
  /\ LET v == CHOOSE x \in candidates : TRUE IN
       /\ decision' = [decision EXCEPT ![p] = v]
       /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est,
                 crashed, crashCount, sent, recv >>

Crash(p) ==
  /\ p \notin crashed
  /\ crashCount < F
  /\ crashed' = crashed \cup {p}
  /\ crashCount' = crashCount + 1
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED << view, prop, est, decision,
                 sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Proc : Broadcast1(p)
  \/ \E p \in Proc, m \in Message : Receive1(p, m)
  \/ \E p \in Proc : Transition1(p)
  \/ \E p \in Proc : Broadcast2(p)
  \/ \E p \in Proc, m \in Message : Receive2(p, m)
  \/ \E p \in Proc, v \in Values : Decide(p, v)
  \/ \E p \in Proc : MoveToChoosing(p)
  \/ \E p \in Proc : Choose(p)
  \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [] [Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ loc \in [Proc -> {"bcast1","wait1","bcast2","wait2","done","crashed","choosing"}]
  /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> (Values \cup {Bottom})]
  /\ decision \in [Proc -> (Values \cup {Bottom})]
  /\ crashed \subseteq Proc
  /\ crashCount = Cardinality(crashed)
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]

Validity ==
  \A p \in Proc :
    decision[p] # Bottom =>
      /\ decision[p] \in Values
      /\ \E q \in Proc : prop[q] = decision[p]

Agreement ==
  \A p, q \in Proc :
    (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====