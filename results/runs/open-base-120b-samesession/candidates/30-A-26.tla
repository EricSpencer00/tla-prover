---- MODULE cbc_max ----
EXTENDS Naturals, Integers, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

(*
  Derived constants
*)
Proc == 1 .. N
PhaseSet == {"broadcast1", "wait1", "broadcast2", "wait2", "done", "crashed", "choosing"}
Msg == [type : {"phase1", "phase2"},
        sender : Proc,
        val    : Values,
        est    : Values]

VARIABLES pc,          \* [Proc -> PhaseSet]
          prop,        \* [Proc -> Values]   (initial proposals)
          est,         \* [Proc -> Values]   (estimated values after phase‑1)
          dec,         \* [Proc -> Values]   (decision values)
          view,        \* [Proc -> [Proc -> Values]]
          msgs,        \* SUBSET Msg   (messages in transit)
          rcv2         \* [Proc -> [Values -> Nat]]  (counts of phase‑2 msgs per estimate)

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
MaxVal(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE v \in Values :
        v \in S /\ \A w \in S : w <= v

RecvCount(p) == Cardinality({ q \in Proc : view[p][q] # Bottom })

TotalRecv(p) == \Sum v \in Values : rcv2[p][v]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Proc |-> "broadcast1"]
  /\ prop = [p \in Proc |-> CHOOSE v \in Values : TRUE]   \* arbitrary proposal
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ msgs = {}
  /\ rcv2 = [p \in Proc |-> [v \in Values |-> 0]]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
  /\ pc[p] = "broadcast1"
  /\ msgs' = msgs \cup {
        [type |-> "phase1",
         sender |-> p,
         val    |-> prop[p],
         est    |-> Bottom]
      }
  /\ pc' = [pc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<prop, est, dec, view, rcv2>>

Receive1 ==
  \E p \in Proc, m \in msgs :
    /\ pc[p] = "wait1"
    /\ m.type = "phase1"
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<pc, prop, est, dec, rcv2>>

ComputeEst(p) ==
  /\ pc[p] = "wait1"
  /\ RecvCount(p) >= N - T
  /\ est' = [est EXCEPT ![p] = MaxVal({ view[p][q] : q \in Proc })]
  /\ pc' = [pc EXCEPT ![p] = "broadcast2"]
  /\ UNCHANGED <<prop, dec, view, msgs, rcv2>>

Broadcast2(p) ==
  /\ pc[p] = "broadcast2"
  /\ msgs' = msgs \cup {
        [type |-> "phase2",
         sender |-> p,
         val    |-> prop[p],
         est    |-> est[p]]
      }
  /\ pc' = [pc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<prop, est, dec, view, rcv2>>

Receive2 ==
  \E p \in Proc, m \in msgs :
    /\ pc[p] = "wait2"
    /\ m.type = "phase2"
    /\ rcv2' = [rcv2 EXCEPT ![p][m.est] = @ + 1]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<pc, prop, est, dec, view>>

Decide(p, v) ==
  /\ pc[p] = "wait2"
  /\ rcv2[p][v] >= N - T
  /\ dec' = [dec EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<prop, est, view, msgs, rcv2>>

MoveToChoosing(p) ==
  /\ pc[p] = "wait2"
  /\ TotalRecv(p) = N
  /\ \A v \in Values : rcv2[p][v] < N - T
  /\ pc' = [pc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<prop, est, dec, view, msgs, rcv2>>

Choose(p) ==
  LET S == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
    /\ pc[p] = "choosing"
    /\ S # {}
    /\ dec' = [dec EXCEPT ![p] = CHOOSE v \in S : TRUE]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<prop, est, view, msgs, rcv2>>

Crash(p) ==
  /\ pc[p] \notin {"crashed", "done"}
  /\ Cardinality({ q \in Proc : pc[q] = "crashed" }) < F
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<prop, est, dec, view, msgs, rcv2>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Proc : Broadcast1(p)
  \/ Receive1
  \/ \E p \in Proc : ComputeEst(p)
  \/ \E p \in Proc : Broadcast2(p)
  \/ Receive2
  \/ \E p \in Proc, v \in Values : Decide(p, v)
  \/ \E p \in Proc : MoveToChoosing(p)
  \/ \E p \in Proc : Choose(p)
  \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, prop, est, dec, view, msgs, rcv2>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> PhaseSet]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> Values]
  /\ dec \in [Proc -> Values]
  /\ view \in [Proc -> [Proc -> Values]]
  /\ msgs \subseteq Msg
  /\ rcv2 \in [Proc -> [Values -> Nat]]
  /\ Bottom \notin Values

Validity ==
  \A p \in Proc :
    pc[p] = "done" =>
      /\ dec[p] \in Values
      /\ \E q \in Proc : dec[p] = prop[q]

Agreement ==
  \A p, q \in Proc :
    (pc[p] = "done" /\ pc[q] = "done") => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* The required identifiers
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

====