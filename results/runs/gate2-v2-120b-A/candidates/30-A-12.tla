---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*--------------------------------------------------------------------
  Constants (provided by the .cfg)
--------------------------------------------------------------------*)
CONSTANTS N, T, F, Values, Bottom

(*--------------------------------------------------------------------
  Derivable sets
--------------------------------------------------------------------*)
ProcSet == 1..N

MessageType == {"phase1", "phase2"}

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    pc,          \* control location of each process
    localView,   \* matrix: for each process, the latest value known from each sender
    proposed,    \* proposed value of each process
    estimated,   \* estimated value after phase 1
    decided,     \* final decision value (Bottom means not decided)
    crashed,     \* number of processes that have crashed
    sentMsgs,    \* set of all messages that have been broadcast
    recvSet      \* set of messages received by each process

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Message == [type : MessageType,
            value : Values,
            sender : ProcSet,
            est : Values \cup {Bottom}]  \* est is Bottom for phase1 msgs

Phase1Msg(m) == /\ m.type = "phase1"
                /\ m.est = Bottom

Phase2Msg(m) == /\ m.type = "phase2"
                /\ m.est \in Values

(* The initial state *)
Init ==
    /\ pc = [p \in ProcSet |-> "broadcastPhase1"]
    /\ proposed = [p \in ProcSet |-> CHOOSE v \in Values : TRUE]  \* nondeterministically assign
    /\ localView = [p \in ProcSet |-> [s \in ProcSet |-> Bottom]]
    /\ estimated = [p \in ProcSet |-> Bottom]
    /\ decided = [p \in ProcSet |-> Bottom]
    /\ crashed = 0
    /\ sentMsgs = {}
    /\ recvSet = [p \in ProcSet |-> {}]

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

BroadcastPhase1(p) ==
    /\ pc[p] = "broadcastPhase1"
    /\ sentMsgs' = sentMsgs \cup { [type |-> "phase1",
                                 value |-> proposed[p],
                                 sender |-> p,
                                 est |-> Bottom] }
    /\ pc' = [pc EXCEPT ![p] = "waitPhase1"]
    /\ UNCHANGED <<localView, proposed, estimated, decided, crashed, recvSet>>

ReceivePhase1(p) ==
    /\ pc[p] = "waitPhase1"
    /\ \E m \in sentMsgs :
          /\ Phase1Msg(m)
          /\ localView[p][m.sender] = Bottom
          /\ localView' = [localView EXCEPT ![p][m.sender] = m.value]
          /\ recvSet' = [recvSet EXCEPT ![p] = recvSet[p] \cup {m}]
    /\ UNCHANGED <<pc, proposed, estimated, decided, crashed, sentMsgs>>

ComputeEst(p) ==
    /\ pc[p] = "waitPhase1"
    /\ Cardinality({s \in ProcSet : localView[p][s] # Bottom}) >= N - T
    /\ estimated' = [estimated EXCEPT ![p] = 
                     Max({localView[p][s] : s \in ProcSet /\ localView[p][s] # Bottom})]
    /\ pc' = [pc EXCEPT ![p] = "broadcastPhase2"]
    /\ UNCHANGED <<localView, proposed, decided, crashed, sentMsgs, recvSet>>

BroadcastPhase2(p) ==
    /\ pc[p] = "broadcastPhase2"
    /\ sentMsgs' = sentMsgs \cup { [type |-> "phase2",
                                 value |-> proposed[p],
                                 sender |-> p,
                                 est |-> estimated[p]] }
    /\ pc' = [pc EXCEPT ![p] = "waitPhase2"]
    /\ UNCHANGED <<localView, proposed, estimated, decided, crashed, recvSet>>

ReceivePhase2(p) ==
    /\ pc[p] = "waitPhase2"
    /\ \E m \in sentMsgs :
          /\ Phase2Msg(m)
          /\ localView[p][m.sender] = Bottom
          /\ localView' = [localView EXCEPT ![p][m.sender] = m.est]
          /\ recvSet' = [recvSet EXCEPT ![p] = recvSet[p] \cup {m}]
    /\ UNCHANGED <<pc, proposed, estimated, decided, crashed, sentMsgs>>

DecideFromEst(p) ==
    /\ pc[p] = "waitPhase2"
    /\ \E v \in Values :
          Cardinality({ m \in recvSet[p] : Phase2Msg(m) /\ m.est = v }) >= N - T
    /\ decided' = [decided EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<localView, proposed, estimated, crashed, sentMsgs, recvSet>>

MoveToChoosing(p) ==
    /\ pc[p] = "waitPhase2"
    /\ Cardinality({ m \in recvSet[p] : Phase2Msg(m) }) = N
    /\ \A v \in Values :
         Cardinality({ m \in recvSet[p] : Phase2Msg(m) /\ m.est = v }) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<localView, proposed, estimated, decided, crashed, sentMsgs, recvSet>>

ChooseAndDecide(p) ==
    /\ pc[p] = "choosing"
    /\ \E v \in Values : v \in {localView[p][s] : s \in ProcSet}
    /\ decided' = [decided EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<localView, proposed, estimated, crashed, sentMsgs, recvSet>>

Crash(p) ==
    /\ pc[p] # "crashed"
    /\ crashed < F
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<localView, proposed, estimated, decided, sentMsgs, recvSet>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ \E p \in ProcSet : BroadcastPhase1(p)
    \/ \E p \in ProcSet : ReceivePhase1(p)
    \/ \E p \in ProcSet : ComputeEst(p)
    \/ \E p \in ProcSet : BroadcastPhase2(p)
    \/ \E p \in ProcSet : ReceivePhase2(p)
    \/ \E p \in ProcSet : DecideFromEst(p)
    \/ \E p \in ProcSet : MoveToChoosing(p)
    \/ \E p \in ProcSet : ChooseAndDecide(p)
    \/ \E p \in ProcSet : Crash(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<pc, localView, proposed, estimated,
                 decided, crashed, sentMsgs, recvSet>>

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ pc \in [ProcSet -> {"broadcastPhase1","waitPhase1",
                           "broadcastPhase2","waitPhase2",
                           "done","crashed","choosing"}]
    /\ localView \in [ProcSet -> [ProcSet -> (Values \cup {Bottom})]]
    /\ proposed \in [ProcSet -> Values]
    /\ estimated \in [ProcSet -> (Values \cup {Bottom})]
    /\ decided \in [ProcSet -> (Values \cup {Bottom})]
    /\ crashed \in Nat
    /\ sentMsgs \subseteq Message
    /\ recvSet \in [ProcSet -> SUBSET Message]

(*--------------------------------------------------------------------
  Safety properties
--------------------------------------------------------------------*)
Validity ==
    \A p \in ProcSet :
        decided[p] # Bottom => decided[p] \in Values

Agreement ==
    \A p, q \in ProcSet :
        /\ decided[p] # Bottom
        /\ decided[q] # Bottom
        => decided[p] = decided[q]

=============================================================================