---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Types and helper definitions
\* ----------------------------------------------------------------------
Locs == {"broadcast1", "wait1", "broadcast2", "wait2",
         "choosing", "done", "crashed"}

Message == [type : {"p1","p2"},
            val  : Values,
            sender: 1..N,
            est  : Values \cup {Bottom}]

MsgP1(val, snd) == [type |-> "p1", val |-> val, sender |-> snd,
                    est |-> Bottom]

MsgP2(val, estVal, snd) == [type |-> "p2", val |-> val,
                            sender |-> snd, est |-> estVal]

\* Max of a non‑empty set of Values (Values are totally ordered)
MaxVal(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE v \in S : \A w \in S : w <= v

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc, propose, view, est, decision,
          crashedCount, sent, recv

vars == <<pc, propose, view, est, decision,
         crashedCount, sent, recv>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in 1..N |-> "broadcast1"]
  /\ propose \in [1..N -> Values]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ est = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
  /\ pc[p] = "broadcast1"
  /\ sent' = sent \cup {MsgP1(propose[p], p)}
  /\ pc' = [pc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<propose, view, est, decision,
                crashedCount, recv>>

Receive1(p) ==
  /\ pc[p] = "wait1"
  /\ \E m \in sent \ setdiff recv[p] :
        /\ m.type = "p1"
        /\ LET sender == m.sender IN
           view' = [view EXCEPT ![p][sender] = m.val]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
        /\ UNCHANGED <<pc, propose, est, decision,
                       crashedCount, sent>>
  /\ UNCHANGED <<pc, propose, est, decision,
                crashedCount, sent>>

Phase1Ready(p) ==
  /\ pc[p] = "wait1"
  /\ Cardinality({ m \in recv[p] : m.type = "p1" }) >= N - T
  /\ LET realVals == ({ view[p][q] : q \in 1..N } \cup {propose[p]}) \ {Bottom} IN
     est' = [est EXCEPT ![p] = MaxVal(realVals)]
  /\ pc' = [pc EXCEPT ![p] = "broadcast2"]
  /\ UNCHANGED <<propose, view, decision,
                crashedCount, sent, recv>>

Broadcast2(p) ==
  /\ pc[p] = "broadcast2"
  /\ sent' = sent \cup {MsgP2(propose[p], est[p], p)}
  /\ pc' = [pc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<propose, view, est, decision,
                crashedCount, recv>>

Receive2(p) ==
  /\ pc[p] = "wait2"
  /\ \E m \in sent \ setdiff recv[p] :
        /\ m.type = "p2"
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
        /\ UNCHANGED <<pc, propose, view, est,
                      decision, crashedCount, sent>>
  /\ UNCHANGED <<pc, propose, view, est,
                decision, crashedCount, sent>>

DecideFromEst(p) ==
  /\ pc[p] = "wait2"
  /\ \E v \in Values :
        Cardinality({ m \in recv[p] :
                       m.type = "p2" /\ m.est = v }) >= N - T
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<propose, view, est,
                crashedCount, sent, recv>>

MoveToChoosing(p) ==
  /\ pc[p] = "wait2"
  /\ Cardinality({ m \in recv[p] : m.type = "p2" }) = N
  /\ \A v \in Values :
        Cardinality({ m \in recv[p] :
                       m.type = "p2" /\ m.est = v }) < N - T
  /\ pc' = [pc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<propose, view, est, decision,
                crashedCount, sent, recv>>

Choose(p) ==
  /\ pc[p] = "choosing"
  /\ \E v \in Values :
        \E q \in 1..N : view[p][q] = v
  /\ LET chosen == CHOOSE v \in Values :
        \E q \in 1..N : view[p][q] = v IN
     decision' = [decision EXCEPT ![p] = chosen]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<propose, view, est,
                crashedCount, sent, recv>>

Crash(p) ==
  /\ pc[p] # "crashed"
  /\ crashedCount < F
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<propose, view, est, decision,
                sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in 1..N : Broadcast1(p)
  \/ \E p \in 1..N : Receive1(p)
  \/ \E p \in 1..N : Phase1Ready(p)
  \/ \E p \in 1..N : Broadcast2(p)
  \/ \E p \in 1..N : Receive2(p)
  \/ \E p \in 1..N : DecideFromEst(p)
  \/ \E p \in 1..N : MoveToChoosing(p)
  \/ \E p \in 1..N : Choose(p)
  \/ \E p \in 1..N : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ N > 0
  /\ 2 * T < N
  /\ 0 <= F /\ F <= T
  /\ pc \in [1..N -> Locs]
  /\ propose \in [1..N -> Values]
  /\ view \in [1..N -> [1..N -> (Values \cup {Bottom})]]
  /\ est \in [1..N -> (Values \cup {Bottom})]
  /\ decision \in [1..N -> (Values \cup {Bottom})]
  /\ crashedCount \in Nat
  /\ crashedCount <= N
  /\ sent \subseteq Message
  /\ recv \in [1..N -> SUBSET Message]
  /\ \A p \in 1..N :
        recv[p] \subseteq sent

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
  \A p \in 1..N :
    decision[p] # Bottom => 
      /\ decision[p] \in Values
      /\ \E q \in 1..N : propose[q] = decision[p]

Agreement ==
  \A p, q \in 1..N :
    /\ decision[p] # Bottom
    /\ decision[q] # Bottom
    => decision[p] = decision[q]

====