---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F, Values, Bottom

(* -------------------------------------------------------------------------- *)
(* Derived constants                                                          *)
(* -------------------------------------------------------------------------- *)
\* The size of the system must be a natural number greater than zero
ASSUME PosN == N \in Nat \ {0}

(* -------------------------------------------------------------------------- *)
(* Variables                                                                  *)
(* -------------------------------------------------------------------------- *)
VARIABLES pc,            \* control point of each process
          proposed,      \* proposed value of each process
          localViews,    \* N->(N->Values) matrix of received values
          estimated,     \* estimated value after phase 1
          decided,       \* decision value (Bottom if not decided)
          crashed,       \* set of crashed processes
          sent,          \* set of all sent messages
          received       \* map from process to set of messages it has received

(* -------------------------------------------------------------------------- *)
(* Types                                                                      *)
(* -------------------------------------------------------------------------- *)
ProcSet == 1..N
Phase1Msg == [type : {"Phase1"}, sender : ProcSet, value : Values]
Phase2Msg == [type : {"Phase2"}, sender : ProcSet,
             proposed : Values, estimated : Values]

Message == Phase1Msg \cup Phase2Msg

TypeOK ==
    /\ pc \in [ProcSet -> {"bcast1", "wait1", "bcast2", "wait2",
                           "done", "crashed", "choosing"}]
    /\ proposed \in [ProcSet -> Values]
    /\ localViews \in [ProcSet -> [ProcSet -> Values]]
    /\ estimated \in [ProcSet -> Values]
    /\ decided \in [ProcSet -> Values]
    /\ crashed \in SUBSET ProcSet
    /\ sent \subseteq Message
    /\ received \in [ProcSet -> SUBSET Message]

(* -------------------------------------------------------------------------- *)
(* Helper definitions                                                         *)
(* -------------------------------------------------------------------------- *)
Max(vs) ==
    IF vs = {} THEN Bottom
    ELSE CHOOSE x \in vs : \A y \in vs : y <= x

Quorum == N - T

(* -------------------------------------------------------------------------- *)
(* Initialization                                                             *)
(* -------------------------------------------------------------------------- *)
Init ==
    /\ pc = [p \in ProcSet |-> "bcast1"]
    /\ proposed \in [ProcSet -> Values]
    /\ localViews = [p \in ProcSet |-> [q \in ProcSet |-> Bottom]]
    /\ estimated = [p \in ProcSet |-> Bottom]
    /\ decided = [p \in ProcSet |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ received = [p \in ProcSet |-> {}]

(* -------------------------------------------------------------------------- *)
(* Actions                                                                    *)
(* -------------------------------------------------------------------------- *)

BroadcastPhase1(p) ==
    /\ pc[p] = "bcast1"
    /\ LET m == [type |-> "Phase1", sender |-> p, value |-> proposed[p]] IN
       /\ sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<proposed, localViews, estimated, decided,
                   crashed, received>>

ReceivePhase1(p) ==
    /\ pc[p] = "wait1"
    /\ \E m \in sent :
          /\ m.type = "Phase1"
          /\ m.sender \notin crashed
          /\ m \notin received[p]
          /\ localViews' = [localViews EXCEPT ![p][m.sender] = m.value]
          /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ UNCHANGED <<pc, proposed, estimated, decided, crashed, sent>>

ComputeEstimated(p) ==
    /\ pc[p] = "wait1"
    /\ Cardinality({s \in ProcSet : localViews[p][s] # Bottom}) >= Quorum
    /\ estimated' = [estimated EXCEPT ![p] = Max({localViews[p][s] :
                                                s \in ProcSet})]
    /\ pc' = [pc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED <<proposed, localViews, decided, crashed, sent, received>>

BroadcastPhase2(p) ==
    /\ pc[p] = "bcast2"
    /\ LET m == [type |-> "Phase2", sender |-> p,
                 proposed |-> proposed[p],
                 estimated |-> estimated[p]] IN
       /\ sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<proposed, localViews, estimated, decided,
                   crashed, received>>

ReceivePhase2(p) ==
    /\ pc[p] = "wait2"
    /\ \E m \in sent :
          /\ m.type = "Phase2"
          /\ m.sender \notin crashed
          /\ m \notin received[p]
          /\ localViews' = [localViews EXCEPT
                             ![p][m.sender] = m.estimated]
          /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ UNCHANGED <<pc, proposed, estimated, decided, crashed, sent>>

DecideByQuorum(p) ==
    /\ pc[p] = "wait2"
    /\ \E v \in Values :
          Cardinality({m \in received[p] :
                      m.type = "Phase2" /\ m.estimated = v}) >= Quorum
    /\ decided' = [decided EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<proposed, localViews, estimated, crashed,
                   sent, received>>

MoveToChoosing(p) ==
    /\ pc[p] = "wait2"
    /\ \A v \in Values :
          Cardinality({m \in received[p] :
                      m.type = "Phase2" /\ m.estimated = v}) < Quorum
    /\ \A s \in ProcSet : s \in { m.sender : m \in received[p] }
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<proposed, localViews, estimated, decided,
                   crashed, sent, received>>

ChooseAndDecide(p) ==
    /\ pc[p] = "choosing"
    /\ \E v \in Values :
          /\ \E s \in ProcSet : localViews[p][s] = v
          /\ decided' = [decided EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<proposed, localViews, estimated, crashed,
                   sent, received>>

Crash(p) ==
    /\ p \notin crashed
    /\ Cardinality(crashed) < F
    /\ crashed' = crashed \cup {p}
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<proposed, localViews, estimated, decided,
                   sent, received>>

Next ==
    \/ \E p \in ProcSet : BroadcastPhase1(p)
    \/ \E p \in ProcSet : ReceivePhase1(p)
    \/ \E p \in ProcSet : ComputeEstimated(p)
    \/ \E p \in ProcSet : BroadcastPhase2(p)
    \/ \E p \in ProcSet : ReceivePhase2(p)
    \/ \E p \in ProcSet : DecideByQuorum(p)
    \/ \E p \in ProcSet : MoveToChoosing(p)
    \/ \E p \in ProcSet : ChooseAndDecide(p)
    \/ \E p \in ProcSet : Crash(p)

(* -------------------------------------------------------------------------- *)
(* Specification                                                              *)
(* -------------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<pc, proposed, localViews, estimated,
                      decided, crashed, sent, received>>

(* -------------------------------------------------------------------------- *)
(* Safety Invariants                                                          *)
(* -------------------------------------------------------------------------- *)
Validity ==
    \A p \in ProcSet :
        decided[p] # Bottom => decided[p] \in Values

Agreement ==
    \A p, q \in ProcSet :
        /\ decided[p] # Bottom
        /\ decided[q] # Bottom
        => decided[p] = decided[q]

(* -------------------------------------------------------------------------- *)
(* Theorems (optional)                                                        *)
(* -------------------------------------------------------------------------- *)
THEOREM Spec => []TypeOK
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

====