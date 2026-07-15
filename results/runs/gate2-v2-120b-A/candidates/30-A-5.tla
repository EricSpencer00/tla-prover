---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
--------------------------------------------------------------------*)
CONSTANT N          \* number of processes
CONSTANT T          \* maximum number of tolerated faults
CONSTANT F          \* actual number of faults (upper bound)
CONSTANT Values     \* finite set of possible proposal values
CONSTANT Bottom     \* special bottom value not in Values

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
ProcSet == 1..N

TypeOkValues == Values \/ {Bottom}

(*--------------------------------------------------------------------
  Message definition
--------------------------------------------------------------------*)
Message == [type  : {"Phase1", "Phase2"},
            sender: ProcSet,
            prop  : TypeOkValues,
            est   : TypeOkValues]  \* 'est' is Bottom for Phase1 messages

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    loc,          \* control location of each process
    view,         \* N-by-N matrix of received values; view[i][j] is value i has about j
    prop,         \* proposed value of each process
    est,          \* estimated value after Phase1
    decided,      \* decision value of each process (Bottom = not decided)
    crashed,      \* set of crashed processes
    sent,         \* set of all messages that have been sent
    recv          \* messages received by each process

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ loc    = [i \in ProcSet |-> "BroadcastPhase1"]
    /\ prop   \in [i \in ProcSet |-> Values]            \* each proposes a value
    /\ est    = [i \in ProcSet |-> Bottom]
    /\ decided= [i \in ProcSet |-> Bottom]
    /\ crashed= {}
    /\ sent   = {}
    /\ recv   = [i \in ProcSet |-> {}]
    /\ view   = [i \in ProcSet |-> [j \in ProcSet |-> Bottom]]

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
MaxValue(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE v \in S : \A w \in S : v >= w

ReceivedFrom(i, mtype) ==
    { m.sender : m \in recv[i] /\ m.type = mtype }

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
BroadcastPhase1(i) ==
    /\ loc[i] = "BroadcastPhase1"
    /\ sent' = sent \cup { [type |-> "Phase1",
                           sender |-> i,
                           prop   |-> prop[i],
                           est    |-> Bottom] }
    /\ loc' = [loc EXCEPT ![i] = "WaitPhase1"]
    /\ UNCHANGED <<view, est, decided, crashed, recv>>

ReceivePhase1(i) ==
    /\ \E m \in sent :
         /\ m.type = "Phase1"
         /\ m.sender \notin crashed
         /\ m.sender \notin ReceivedFrom(i, "Phase1")
    /\ view' = [view EXCEPT ![i][m.sender] = m.prop]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED <<loc, est, decided, crashed, sent, prop>>

WaitPhase1ToPhase2(i) ==
    /\ loc[i] = "WaitPhase1"
    /\ Cardinality(ReceivedFrom(i, "Phase1")) >= N - T
    /\ est' = [est EXCEPT ![i] = MaxValue({ view[i][j] : j \in ProcSet })]
    /\ loc' = [loc EXCEPT ![i] = "BroadcastPhase2"]
    /\ UNCHANGED <<view, decided, crashed, sent, recv, prop>>

BroadcastPhase2(i) ==
    /\ loc[i] = "BroadcastPhase2"
    /\ sent' = sent \cup { [type |-> "Phase2",
                           sender |-> i,
                           prop   |-> prop[i],
                           est    |-> est[i]] }
    /\ loc' = [loc EXCEPT ![i] = "WaitPhase2"]
    /\ UNCHANGED <<view, est, decided, crashed, recv, prop>>

ReceivePhase2(i) ==
    /\ \E m \in sent :
         /\ m.type = "Phase2"
         /\ m.sender \notin crashed
         /\ m.sender \notin ReceivedFrom(i, "Phase2")
    /\ view' = [view EXCEPT ![i][m.sender] = m.est]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED <<loc, est, decided, crashed, sent, prop>>

DecideFromPhase2(i) ==
    /\ loc[i] = "WaitPhase2"
    /\ \E v \in TypeOkValues :
         Cardinality({ m \in recv[i] : m.type = "Phase2" /\ m.est = v }) >= N - T
    /\ decided' = [decided EXCEPT ![i] = v]
    /\ loc' = [loc EXCEPT ![i] = "Done"]
    /\ UNCHANGED <<view, est, crashed, sent, recv, prop>>

MoveToChoosing(i) ==
    /\ loc[i] = "WaitPhase2"
    /\ Cardinality({ m : m \in recv[i] /\ m.type = "Phase2" }) = N
    /\ \A v \in TypeOkValues :
         Cardinality({ m \in recv[i] : m.type = "Phase2" /\ m.est = v }) < N - T
    /\ loc' = [loc EXCEPT ![i] = "Choosing"]
    /\ UNCHANGED <<view, est, decided, crashed, sent, recv, prop>>

ChooseAndDecide(i) ==
    /\ loc[i] = "Choosing"
    /\ \E v \in TypeOkValues :
         v # Bottom /\ \E j \in ProcSet : view[i][j] = v
    /\ decided' = [decided EXCEPT ![i] = v]
    /\ loc' = [loc EXCEPT ![i] = "Done"]
    /\ UNCHANGED <<view, est, crashed, sent, recv, prop>>

Crash(i) ==
    /\ i \notin crashed
    /\ Cardinality(crashed) < F
    /\ crashed' = crashed \cup {i}
    /\ loc' = [loc EXCEPT ![i] = "Crashed"]
    /\ UNCHANGED <<view, est, decided, sent, recv, prop>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ \E i \in ProcSet : BroadcastPhase1(i)
    \/ \E i \in ProcSet : ReceivePhase1(i)
    \/ \E i \in ProcSet : WaitPhase1ToPhase2(i)
    \/ \E i \in ProcSet : BroadcastPhase2(i)
    \/ \E i \in ProcSet : ReceivePhase2(i)
    \/ \E i \in ProcSet : DecideFromPhase2(i)
    \/ \E i \in ProcSet : MoveToChoosing(i)
    \/ \E i \in ProcSet : ChooseAndDecide(i)
    \/ \E i \in ProcSet : Crash(i)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<loc, view, prop, est, decided, crashed, sent, recv>>

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ loc \in [ProcSet -> {"BroadcastPhase1","WaitPhase1","BroadcastPhase2",
                           "WaitPhase2","Choosing","Done","Crashed"}]
    /\ prop \in [ProcSet -> Values]
    /\ est \in [ProcSet -> TypeOkValues]
    /\ decided \in [ProcSet -> TypeOkValues]
    /\ crashed \subseteq ProcSet
    /\ sent \subseteq Message
    /\ recv \in [ProcSet -> SUBSET Message]
    /\ view \in [ProcSet -> [ProcSet -> TypeOkValues]]

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
Validity ==
    \A i \in ProcSet :
        decided[i] # Bottom => decided[i] \in Values

Agreement ==
    \A i, j \in ProcSet :
        /\ decided[i] # Bottom
        /\ decided[j] # Bottom
        => decided[i] = decided[j]

=============================================================================