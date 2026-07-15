---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(* Constants as required by the cfg file                                   *)
(***************************************************************************)
CONSTANT N, T, F

(***************************************************************************)
(* Derived sets                                                            *)
(***************************************************************************)
Proc == 1..N
Correct == CorrectSet
Faulty  == FaultySet

(***************************************************************************)
(* Message type                                                            *)
(***************************************************************************)
MessageType == {"ECHO"}

Message == [type : MessageType, sender : Proc]

(***************************************************************************)
(* Control locations (program counters)                                    *)
(***************************************************************************)
CtrlLoc == {"Idle", "SentECHO", "Accepted"}

(***************************************************************************)
(* Variables                                                               *)
(***************************************************************************)
VARIABLES correctSet, faultySet, ctrl, sent, rcvd

\* ctrl[p] \in CtrlLoc indicates the state of process p
\* sent \subseteq Message   set of messages that have been sent (by correct processes)
\* rcvd[p] \subseteq Message   messages that process p has received

(***************************************************************************)
(* Helper definitions                                                      *)
(***************************************************************************)
InitCorrectSet == {p \in Proc : p <= N - F}
InitFaultySet  == Proc \ {InitCorrectSet}

InitCtrl(p) ==
  IF p \in correctSet
     THEN IF p \in InitCorrectSetInitRecv THEN "Idle" ELSE "Idle"
     ELSE "Idle"

\* For the safety (unforgeability) configuration we need a variant where no
\* correct process receives INIT.  We'll model this by a constant that tells
\* whether the "broadcast-received" flag is true for each correct process.
\* The flag is only used in the initial state; after that the protocol ignores it.
CONSTANT InitBroadcastReceived \* a subset of Correct indicating which start with INIT

(* For the safety configuration the constant will be {} *)
(* For the liveness configuration it will be Correct *)

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)
Init ==
  /\ correctSet = InitCorrectSet
  /\ faultySet  = InitFaultySet
  /\ ctrl       = [p \in Proc |-> "Idle"]
  /\ sent       = {}
  /\ rcvd       = [p \in Proc |-> {}]

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* A correct process may receive any subset of messages that have been sent
\* by correct processes or arbitrary messages from Byzantine processes.
Receive(p) ==
  /\ p \in correctSet
  /\ rcvd[p]' = rcvd[p] \cup Subset( sent \cup { [type |-> "ECHO", sender |-> b] : b \in faultySet } )
  /\ UNCHANGED <<correctSet, faultySet, ctrl, sent>>

SendECHO(p) ==
  /\ p \in correctSet
  /\ ctrl[p] = "Idle"
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ ctrl' = [ctrl EXCEPT ![p] = "SentECHO"]
  /\ UNCHANGED <<correctSet, faultySet, rcvd>>

Accept(p) ==
  /\ p \in correctSet
  /\ ctrl[p] # "Accepted"
  /\ ctrl' = [ctrl EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<correctSet, faultySet, sent, rcvd>>

\* Transition for a process that already sent ECHO and later receives enough ECHOs
AcceptIfEnoughECHO(p) ==
  LET echoSenders == { m.sender : m \in rcvd[p] /\ m.type = "ECHO" } IN
  /\ p \in correctSet
  /\ ctrl[p] = "SentECHO"
  /\ Cardinality(echoSenders) >= N - T
  /\ Accept(p)

\* Transition for a process that has not yet sent ECHO but receives many ECHOs
SendECHOIfEnough(p) ==
  LET echoSenders == { m.sender : m \in rcvd[p] /\ m.type = "ECHO" } IN
  /\ p \in correctSet
  /\ ctrl[p] = "Idle"
  /\ Cardinality(echoSenders) >= N - 2*T
  /\ IF Cardinality(echoSenders) >= N - T
        THEN /\ SendECHO(p)
             /\ Accept(p)
        ELSE SendECHO(p)

\* Immediate accept for processes that start with the broadcast (INIT) flag
InitAcceptAndEcho(p) ==
  /\ p \in correctSet
  /\ p \in InitBroadcastReceived
  /\ ctrl[p] = "Idle"
  /\ SendECHO(p)
  /\ Accept(p)

\* Next-state relation
Next ==
  \/ \E p \in correctSet : Receive(p)
  \/ \E p \in correctSet : InitAcceptAndEcho(p)
  \/ \E p \in correctSet : SendECHOIfEnough(p)
  \/ \E p \in correctSet : AcceptIfEnoughECHO(p)
  \/ UNCHANGED <<correctSet, faultySet, ctrl, sent, rcvd>>

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<ctrl, sent, rcvd, correctSet, faultySet>>

(***************************************************************************)
(* Type correctness invariant (TypeOK)                                    *)
(***************************************************************************)
TypeOK ==
  /\ correctSet \subseteq Proc
  /\ faultySet  \subseteq Proc
  /\ correctSet \cap faultySet = {}
  /\ ctrl \in [Proc -> CtrlLoc]
  /\ sent \subseteq Message
  /\ rcvd \in [Proc -> SUBSET Message]

(***************************************************************************)
(* Safety constraints (FCConstraints)                                      *)
(***************************************************************************)
FCConstraints ==
  /\ Cardinality(correctSet) = N - F
  /\ Cardinality(faultySet)  = F
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

(***************************************************************************)
(* Liveness properties (as temporal formulas)                              *)
(***************************************************************************)
CorrLtl ==
  /\ \A p \in correctSet : p \in InitBroadcastReceived
  => <> (\A p \in correctSet : ctrl[p] = "Accepted")

RelayLtl ==
  <> (\E p \in correctSet : ctrl[p] = "Accepted")
    => <> (\A p \in correctSet : ctrl[p] = "Accepted")

UnforgLtl ==
  /\ InitBroadcastReceived = {}
  => [] (\A p \in correctSet : ctrl[p] # "Accepted")

=============================================================================