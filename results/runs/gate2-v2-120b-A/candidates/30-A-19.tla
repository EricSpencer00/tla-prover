---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

(*--------------------------------------------------------------------
  Constants (must be provided in the .cfg file)
--------------------------------------------------------------------*)
CONSTANT N               \* number of processes
CONSTANT T               \* maximum tolerated faults
CONSTANT F               \* actual fault bound (F <= T)
CONSTANT Values          \* finite set of proposed values
CONSTANT Bottom          \* special bottom value not in Values

(*--------------------------------------------------------------------
  Derived sets and helper definitions
--------------------------------------------------------------------*)
ProcSet == 1..N

MsgType == {"phase1", "phase2"}

Message == [type : MsgType,
            sender : ProcSet,
            proposed : Values,
            est : Values \cup {Bottom}]

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES pc,            \* control location per process
          view,          \* N-by-N matrix of received proposed values
          proposed,      \* proposed value per process
          est,           \* estimated value per process
          dec,           \* decision value per process (or Bottom)
          crashed,       \* set of crashed processes
          sent,          \* set of messages that have been sent
          recv           \* set of messages each process has received

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Locs == {"bcast1", "wait1", "bcast2", "wait2",
         "choose", "done", "crash"}

(* Maximum of a set of values, defined for non‑empty sets *)
Max(S) == IF S = {} THEN Bottom ELSE
          CHOOSE x \in S : \A y \in S : y <= x

(* Count of distinct senders in a set of messages *)
Senders(ms) == { m.sender : m \in ms }

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)
Init ==
  /\ pc = [i \in ProcSet |-> "bcast1"]
  /\ proposed = [i \in ProcSet |-> CHOOSE v \in Values : TRUE]  \* nondeterministic selection
  /\ view = [i \in ProcSet |-> [j \in ProcSet |-> Bottom]]
  /\ est = [i \in ProcSet |-> Bottom]
  /\ dec = [i \in ProcSet |-> Bottom]
  /\ crashed = {}
  /\ sent = {}
  /\ recv = [i \in ProcSet |-> {}]

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
BcastPhase1 ==
  /\ \E i \in ProcSet \ (pc[i] = "bcast1")
  /\ LET i == CHOOSE j \in ProcSet : pc[j] = "bcast1" IN
        /\ sent' = sent \cup { [type |-> "phase1",
                               sender |-> i,
                               proposed |-> proposed[i],
                               est |-> Bottom] }
        /\ pc' = [pc EXCEPT ![i] = "wait1"]
        /\ UNCHANGED <<view, proposed, est, dec, crashed, recv>>

ReceivePhase1 ==
  /\ \E i \in ProcSet \ (pc[i] = "wait1" /\ i \notin crashed)
  /\ \E m \in sent :
        /\ m.type = "phase1"
        /\ m.sender \notin crashed
        /\ view[i][m.sender] = Bottom
  /\ LET i == CHOOSE j \in ProcSet : pc[j] = "wait1" /\ j \notin crashed,
          m == CHOOSE msg \in sent :
                msg.type = "phase1" /\ msg.sender \notin crashed /\ view[i][msg.sender] = Bottom
     IN
        /\ view' = [view EXCEPT ![i][m.sender] = m.proposed]
        /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
        /\ UNCHANGED <<pc, proposed, est, dec, crashed, sent>>

ComputeEstAndBcastPhase2 ==
  /\ \E i \in ProcSet :
        /\ pc[i] = "wait1"
        /\ i \notin crashed
        /\ Cardinality(Senders({ m \in recv[i] : m.type = "phase1" })) >= N - T
  /\ LET i == CHOOSE j \in ProcSet :
                pc[j] = "wait1" /\ j \notin crashed /\
                Cardinality(Senders({ m \in recv[j] : m.type = "phase1" })) >= N - T
     IN
        /\ est' = [est EXCEPT ![i] = Max({ view[i][k] : k \in ProcSet })]
        /\ pc' = [pc EXCEPT ![i] = "bcast2"]
        /\ sent' = sent \cup { [type |-> "phase2",
                                 sender |-> i,
                                 proposed |-> proposed[i],
                                 est |-> est[i]] }
        /\ UNCHANGED <<view, proposed, dec, crashed, recv>>

ReceivePhase2 ==
  /\ \E i \in ProcSet : pc[i] = "wait2" /\ i \notin crashed
  /\ \E m \in sent :
        /\ m.type = "phase2"
        /\ m.sender \notin crashed
  /\ LET i == CHOICE i \in ProcSet :
                pc[i] = "wait2" /\ i \notin crashed,
          m == CHOICE msg \in sent :
                msg.type = "phase2" /\ msg.sender \notin crashed
     IN
        /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
        /\ UNCHANGED <<pc, view, proposed, est, dec, crashed, sent>>

DecideFromPhase2 ==
  /\ \E i \in ProcSet : pc[i] = "wait2" /\ i \notin crashed
  /\ \E v \in Values :
        /\ Cardinality({ m \in recv[i] : m.type = "phase2" /\ m.est = v }) >= N - T
  /\ LET i == CHOICE i \in ProcSet :
                pc[i] = "wait2" /\ i \notin crashed,
          v == CHOICE val \in Values :
                Cardinality({ m \in recv[i] : m.type = "phase2" /\ m.est = val }) >= N - T
     IN
        /\ dec' = [dec EXCEPT ![i] = v]
        /\ pc' = [pc EXCEPT ![i] = "done"]
        /\ UNCHANGED <<view, proposed, est, crashed, sent, recv>>

MoveToChoosing ==
  /\ \E i \in ProcSet :
        /\ pc[i] = "wait2"
        /\ i \notin crashed
        /\ Cardinality(Senders({ m \in recv[i] : m.type = "phase2" })) = N
        /\ \A v \in Values :
              Cardinality({ m \in recv[i] : m.type = "phase2" /\ m.est = v }) < N - T
  /\ LET i == CHOICE j \in ProcSet :
                pc[j] = "wait2" /\ j \notin crashed /\
                Cardinality(Senders({ m \in recv[j] : m.type = "phase2" })) = N /\
                \A v \in Values :
                  Cardinality({ m \in recv[j] : m.type = "phase2" /\ m.est = v }) < N - T
     IN
        /\ pc' = [pc EXCEPT ![i] = "choose"]
        /\ UNCHANGED <<view, proposed, est, dec, crashed, sent, recv>>

ChooseAndDecide ==
  /\ \E i \in ProcSet : pc[i] = "choose" /\ i \notin crashed
  /\ LET i == CHOICE j \in ProcSet : pc[j] = "choose" /\ j \notin crashed IN
        /\ \E v \in Values :
              v \in { view[i][k] : k \in ProcSet }
        /\ LET v == CHOICE val \in Values : val \in { view[i][k] : k \in ProcSet }
           IN
              /\ dec' = [dec EXCEPT ![i] = v]
              /\ pc' = [pc EXCEPT ![i] = "done"]
              /\ UNCHANGED <<view, proposed, est, crashed, sent, recv>>

Crash ==
  /\ \E i \in ProcSet :
        /\ i \notin crashed
        /\ Cardinality(crashed) < F
  /\ LET i == CHOICE j \in ProcSet : j \notin crashed /\ Cardinality(crashed) < F IN
        /\ crashed' = crashed \cup {i}
        /\ pc' = [pc EXCEPT ![i] = "crash"]
        /\ UNCHANGED <<view, proposed, est, dec, sent, recv>>

DoneStutter ==
  /\ \A i \in ProcSet : pc[i] \in {"done", "crash"}
  /\ UNCHANGED <<pc, view, proposed, est, dec, crashed, sent, recv>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
  \/ BcastPhase1
  \/ ReceivePhase1
  \/ ComputeEstAndBcastPhase2
  \/ ReceivePhase2
  \/ DecideFromPhase2
  \/ MoveToChoosing
  \/ ChooseAndDecide
  \/ Crash
  \/ DoneStutter

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<pc, view, proposed, est, dec, crashed, sent, recv>>

(*--------------------------------------------------------------------
  Type invariants (optional but useful)
--------------------------------------------------------------------*)
TypeOK ==
  /\ pc \in [ProcSet -> Locs]
  /\ view \in [ProcSet -> [ProcSet -> (Values \cup {Bottom})]]
  /\ proposed \in [ProcSet -> Values]
  /\ est \in [ProcSet -> (Values \cup {Bottom})]
  /\ dec \in [ProcSet -> (Values \cup {Bottom})]
  /\ crashed \subseteq ProcSet
  /\ sent \subseteq Message
  /\ recv \in [ProcSet -> SUBSET Message]

(*--------------------------------------------------------------------
  Safety properties
--------------------------------------------------------------------*)
Validity ==
  \A i \in ProcSet :
    dec[i] # Bottom => dec[i] \in Values

Agreement ==
  \A i, j \in ProcSet :
    (dec[i] # Bottom /\ dec[j] # Bottom) => dec[i] = dec[j]

=============================================================================