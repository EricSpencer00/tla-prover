---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, T, F, Values, Bottom

ASSUME 
    /\ N > 0
    /\ 2 * T < N
    /\ 0 <= F /\ F <= T
    /\ Bottom \\notin Values
    /\ IsFinite(Values)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == 1..N
PC   == {"b1", "w1", "b2", "w2", "choose", "done", "crashed"}
MsgType == {"p1", "p2"}

Message == [type : MsgType,
            sender : Proc,
            value : Values,
            est   : Values]   \* for p1 messages, est = Bottom

VARIABLE pc, view, prop, est, dec, crashed, msgs, rcv

vars == << pc, view, prop, est, dec, crashed, msgs, rcv >>

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
MaxSet(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE v \in S : \A w \in S : w <= v

MaxView(p) ==
  LET vals == { view[p][q] : q \in Proc } IN
    MaxSet(vals)

ReceivedFrom(p, mtype) ==
  { m.sender : m \in rcv[p] /\ m.type = mtype }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Proc |-> "b1"]
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ prop = [p \in Proc |-> CHOOSE v \in Values]   \* arbitrary proposal
  /\ est  = [p \in Proc |-> Bottom]
  /\ dec  = [p \in Proc |-> Bottom]
  /\ crashed = {}
  /\ msgs = {}
  /\ rcv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
  /\ pc[p] = "b1"
  /\ LET m == [type |-> "p1", sender |-> p,
               value |-> prop[p], est |-> Bottom] IN
       msgs' = msgs \cup {m}
  /\ pc' = [pc EXCEPT ![p] = "w1"]
  /\ UNCHANGED << view, prop, est, dec, crashed, rcv >>

ReceivePhase1(p) ==
  /\ pc[p] = "w1"
  /\ \E m \in msgs :
        /\ m.type = "p1"
        /\ m.sender \notin ReceivedFrom(p, "p1")
        /\ view' = [view EXCEPT ![p][m.sender] = m.value]
        /\ rcv'  = [rcv  EXCEPT ![p] = rcv[p] \cup {m}]
        /\ UNCHANGED << pc, prop, est, dec, crashed, msgs >>
        
Phase1ToPhase2(p) ==
  /\ pc[p] = "w1"
  /\ Cardinality(ReceivedFrom(p, "p1")) >= N - T
  /\ est' = [est EXCEPT ![p] = MaxView(p)]
  /\ pc'  = [pc  EXCEPT ![p] = "b2"]
  /\ UNCHANGED << view, prop, dec, crashed, msgs, rcv >>

BroadcastPhase2(p) ==
  /\ pc[p] = "b2"
  /\ LET m == [type |-> "p2", sender |-> p,
               value |-> prop[p], est |-> est[p]] IN
       msgs' = msgs \cup {m}
  /\ pc' = [pc EXCEPT ![p] = "w2"]
  /\ UNCHANGED << view, prop, est, dec, crashed, rcv >>

ReceivePhase2(p) ==
  /\ pc[p] = "w2"
  /\ \E m \in msgs :
        /\ m.type = "p2"
        /\ m.sender \notin ReceivedFrom(p, "p2")
        /\ view' = [view EXCEPT ![p][m.sender] = m.value]
        /\ rcv'  = [rcv  EXCEPT ![p] = rcv[p] \cup {m}]
        /\ UNCHANGED << pc, prop, est, dec, crashed, msgs >>

DecideByThreshold(p) ==
  /\ pc[p] = "w2"
  /\ \E v \in Values :
        /\ Cardinality({ m \in rcv[p] : m.type = "p2" /\ m.est = v }) >= N - T
  /\ dec' = [dec EXCEPT ![p] = v]
  /\ pc'  = [pc  EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashed, msgs, rcv >>

MoveToChoose(p) ==
  /\ pc[p] = "w2"
  /\ (\A v \in Values :
        Cardinality({ m \in rcv[p] : m.type = "p2" /\ m.est = v }) < N - T)
  /\ ReceivedFrom(p, "p2") = Proc    \* all N messages received
  /\ pc' = [pc EXCEPT ![p] = "choose"]
  /\ UNCHANGED << view, prop, est, dec, crashed, msgs, rcv >>

ChooseAndDecide(p) ==
  /\ pc[p] = "choose"
  /\ LET vals == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
        vals # {}
  /\ \E v \in vals :
        /\ dec' = [dec EXCEPT ![p] = v]
        /\ pc'  = [pc  EXCEPT ![p] = "done"]
        /\ UNCHANGED << view, prop, est, crashed, msgs, rcv >>

Crash(p) ==
  /\ p \notin crashed
  /\ Cardinality(crashed) < F
  /\ crashed' = crashed \cup {p}
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED << view, prop, est, dec, msgs, rcv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Proc : BroadcastPhase1(p)
  \/ \E p \in Proc : ReceivePhase1(p)
  \/ \E p \in Proc : Phase1ToPhase2(p)
  \/ \E p \in Proc : BroadcastPhase2(p)
  \/ \E p \in Proc : ReceivePhase2(p)
  \/ \E p \in Proc : DecideByThreshold(p)
  \/ \E p \in Proc : MoveToChoose(p)
  \/ \E p \in Proc : ChooseAndDecide(p)
  \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* State invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> PC]
  /\ view \in [Proc -> [Proc -> Value]]
  /\ prop \in [Proc -> Values]
  /\ est  \in [Proc -> Value]
  /\ dec  \in [Proc -> Value]
  /\ crashed \subseteq Proc
  /\ msgs \subseteq Message
  /\ rcv \in [Proc -> SUBSET Message]
  /\ \A m \in msgs : 
        /\ m.type \in MsgType
        /\ m.sender \in Proc
        /\ m.value \in Values
        /\ m.est \in Value

Validity ==
  \A p \in Proc : dec[p] # Bottom => dec[p] \in Values

Agreement ==
  \A p, q \in Proc :
        (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====