---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

\* ---------- Basic sets ----------
Proc == 1 .. N

Loc == {"broadcast1", "wait1", "broadcast2", "wait2",
        "choosing", "done", "crashed"}

Phase1Msg == [type : "p1", sender : Proc, val : Values]
Phase2Msg == [type : "p2", sender : Proc, val : Values, est : Values]
Msg       == Phase1Msg \cup Phase2Msg

\* ---------- Helper functions ----------
MaxInSet(S) == IF S = {} THEN Bottom ELSE Max(S)

\* ---------- Variables ----------
VARIABLES loc, view, prop, est, dec, crashed, sent, recv

\* ---------- Initial state ----------
Init ==
    /\ loc = [p \in Proc |-> "broadcast1"]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ prop = [p \in Proc |-> CHOOSE v \in Values : TRUE]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ---------- Actions ----------
Broadcast1(p) ==
    /\ loc[p] = "broadcast1"
    /\ UNCHANGED << view, prop, est, dec, crashed, recv >>
    /\ sent' = sent \cup { [type |-> "p1", sender |-> p, val |-> prop[p]] }
    /\ loc' = [loc EXCEPT ![p] = "wait1"]

Receive1(p, m) ==
    /\ loc[p] = "wait1"
    /\ m \in sent
    /\ m.type = "p1"
    /\ m.sender \notin recv[p]
    /\ UNCHANGED << prop, est, dec, crashed, sent >>
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ loc' = loc

Transition1(p) ==
    /\ loc[p] = "wait1"
    /\ Cardinality({ m.sender : m \in recv[p] /\ m.type = "p1" }) >= N - T
    /\ UNCHANGED << view, prop, sent, recv, dec, crashed >>
    /\ est' = [est EXCEPT ![p] = MaxInSet({ view[p][q] : q \in Proc })]
    /\ loc' = [loc EXCEPT ![p] = "broadcast2"]

Broadcast2(p) ==
    /\ loc[p] = "broadcast2"
    /\ UNCHANGED << view, prop, est, dec, crashed, recv >>
    /\ sent' = sent \cup { [type |-> "p2", sender |-> p,
                           val  |-> prop[p], est |-> est[p]] }
    /\ loc' = [loc EXCEPT ![p] = "wait2"]

Receive2(p, m) ==
    /\ loc[p] = "wait2"
    /\ m \in sent
    /\ m.type = "p2"
    /\ m.sender \notin recv[p]
    /\ UNCHANGED << prop, est, dec, crashed, sent >>
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ view' = [view EXCEPT ![p][m.sender] = m.est]
    /\ loc' = loc

MoveToChoosing(p) ==
    /\ loc[p] = "wait2"
    /\ Cardinality({ m.sender : m \in recv[p] /\ m.type = "p2" }) = N
    /\ \A v \in Values :
          Cardinality({ m \in recv[p] : m.type = "p2" /\ m.est = v }) < N - T
    /\ UNCHANGED << view, prop, est, dec, sent, recv, crashed >>
    /\ loc' = [loc EXCEPT ![p] = "choosing"]

Choose(p) ==
    /\ loc[p] = "choosing"
    /\ LET cand == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
       cand # {}
    /\ UNCHANGED << view, prop, est, sent, recv, crashed >>
    /\ dec' = [dec EXCEPT ![p] = CHOOSE v \in cand : TRUE]
    /\ loc' = [loc EXCEPT ![p] = "done"]

Transition2Decide(p) ==
    /\ \E v \in Values :
         /\ loc[p] = "wait2"
         /\ Cardinality({ m \in recv[p] : m.type = "p2" /\ m.est = v }) >= N - T
         /\ UNCHANGED << view, prop, est, sent, recv, crashed >>
         /\ dec' = [dec EXCEPT ![p] = v]
         /\ loc' = [loc EXCEPT ![p] = "done"]

Crash(p) ==
    /\ p \notin crashed
    /\ Cardinality(crashed) < F
    /\ UNCHANGED << view, prop, est, dec, sent, recv >>
    /\ crashed' = crashed \cup {p}
    /\ loc' = [loc EXCEPT ![p] = "crashed"]

Next ==
    \/ \E p \in Proc : Broadcast1(p)
    \/ \E p \in Proc : \E m \in sent : Receive1(p, m)
    \/ \E p \in Proc : Transition1(p)
    \/ \E p \in Proc : Broadcast2(p)
    \/ \E p \in Proc : \E m \in sent : Receive2(p, m)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Transition2Decide(p)
    \/ \E p \in Proc : Crash(p)

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<loc, view, prop, est, dec, crashed, sent, recv>>

\* ---------- Invariants ----------
TypeOK ==
    /\ loc \in [Proc -> Loc]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ dec \in [Proc -> (Values \cup {Bottom})]
    /\ crashed \subseteq Proc
    /\ sent \subseteq Msg
    /\ recv \in [Proc -> SUBSET Msg]
    /\ \A m \in sent :
         (m.type = "p1" => /\ m.val \in Values /\ m.sender \in Proc)
         /\ (m.type = "p2" => /\ m.val \in Values /\ m.est \in Values /\ m.sender \in Proc)

Validity ==
    \A p \in Proc :
        /\ dec[p] # Bottom
        => /\ dec[p] \in Values
           /\ \E q \in Proc : prop[q] = dec[p]

Agreement ==
    \A p, q \in Proc :
        /\ dec[p] # Bottom /\ dec[q] # Bottom
        => dec[p] = dec[q]

\* ---------- The required identifiers ----------
CONSTANTS N, T, F, Values, Bottom
SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT Validity
INVARIANT Agreement

====