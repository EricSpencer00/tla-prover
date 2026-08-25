---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

(* -------------------------------------------------------------------------- *)
(*   Definitions                                                            *)
(* -------------------------------------------------------------------------- *)

PROC == 1 .. N

Message == [type : {"ECHO"}, sender : PROC]

(* -------------------------------------------------------------------------- *)
(*   Variables                                                               *)
(* -------------------------------------------------------------------------- *)

VARIABLES Correct, Faulty, pc, recv, sent

vars == <<Correct, Faulty, pc, recv, sent>>

(* -------------------------------------------------------------------------- *)
(*   Helper definitions                                                      *)
(* -------------------------------------------------------------------------- *)

CorrectSet == { p \in PROC : p \in Correct }
FaultySet  == { p \in PROC : p \in Faulty }

InitState == (pc[p] = IF p \in InitBroadcast then "broadcast" ELSE "noInit")

InitBroadcast == { p \in Correct : p \in InitBroadcast }

InitBroadcast == {}

InitBroadcast == {}

(* The set of all possible ECHO messages that could be sent by Byzantine
   processes (they are not recorded in ''sent''). *)
ByzMsgs == { [type |-> "ECHO", sender |-> b] : b \in FaultySet }

(* Distinct senders of ECHO messages received by process p *)
EchoSenders(p) == { m.sender : m \in recv[p] /\ m.type = "ECHO" }

EchoCount(p) == Cardinality(EchoSenders(p))

(* -------------------------------------------------------------------------- *)
(*   Initial state                                                          *)
(* -------------------------------------------------------------------------- *)

Init ==
    /\ Correct \subseteq PROC
    /\ Cardinality(Correct) = N - F
    /\ Faulty = PROC \ Correct
    /\ pc \in [PROC -> {"noInit", "broadcast", "echoSent", "accept"}]
    /\ \A p \in Correct :
          pc[p] \in {"noInit", "broadcast"}
    /\ \A p \in Faulty :
          pc[p] = "noInit"   \* (value irrelevant for faulty processes)
    /\ recv \in [PROC -> SUBSET Message]
    /\ \A p \in PROC : recv[p] = {}
    /\ sent = {}

(* -------------------------------------------------------------------------- *)
(*   Actions                                                                 *)
(* -------------------------------------------------------------------------- *)

(* A correct process may receive any subset of messages that are currently
   sent by correct processes together with any messages that a Byzantine
   process could forge. *)
Receive(p) ==
    /\ p \in Correct
    /\ LET possible == sent \cup ByzMsgs IN
       /\ new \subseteq possible \ setminus recv[p]
       /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
    /\ UNCHANGED <<Correct, Faulty, pc, sent>>

(* If a correct process started with the INIT message, it immediately
   accepts and sends an ECHO. *)
BroadcastAcceptSend(p) ==
    /\ p \in Correct
    /\ pc[p] = "broadcast"
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
    /\ pc' = [pc EXCEPT ![p] = "accept"]
    /\ UNCHANGED <<Correct, Faulty, recv>>

(* A correct process that has not yet sent ECHO and has received at least
   N-2T distinct ECHO messages (but fewer than N-T) sends ECHO but does not
   accept yet. *)
ThresholdSend(p) ==
    /\ p \in Correct
    /\ pc[p] = "noInit"
    /\ EchoCount(p) >= N - 2*T
    /\ EchoCount(p) <  N - T
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
    /\ pc' = [pc EXCEPT ![p] = "echoSent"]
    /\ UNCHANGED <<Faulty, recv>>

(* A correct process that has not yet sent ECHO and has received at least
   N-T distinct ECHO messages sends ECHO (if not already sent) and accepts. *)
ThresholdSendAccept(p) ==
    /\ p \in Correct
    /\ pc[p] = "noInit"
    /\ EchoCount(p) >= N - T
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
    /\ pc' = [pc EXCEPT ![p] = "accept"]
    /\ UNCHANGED <<Faulty, recv>>

(* A correct process that already sent ECHO accepts once it has received
   at least N-T distinct ECHO messages. *)
AcceptAfterEcho(p) ==
    /\ p \in Correct
    /\ pc[p] = "echoSent"
    /\ EchoCount(p) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "accept"]
    /\ UNCHANGED <<Correct, Faulty, recv, sent>>

(* -------------------------------------------------------------------------- *)
(*   Next relation                                                            *)
(* -------------------------------------------------------------------------- *)

Next ==
    \/ \E p \in Correct : Receive(p)
    \/ \E p \in Correct : BroadcastAcceptSend(p)
    \/ \E p \in Correct : ThresholdSend(p)
    \/ \E p \in Correct : ThresholdSendAccept(p)
    \/ \E p \in Correct : AcceptAfterEcho(p)

(* -------------------------------------------------------------------------- *)
(*   Specification                                                            *)
(* -------------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars

(* -------------------------------------------------------------------------- *)
(*   Type correctness invariant                                              *)
(* -------------------------------------------------------------------------- *)

TypeOK ==
    /\ Correct \subseteq PROC
    /\ Cardinality(Correct) = N - F
    /\ Faulty = PROC \ Correct
    /\ pc \in [PROC -> {"noInit", "broadcast", "echoSent", "accept"}]
    /\ \A p \in Correct :
          pc[p] \in {"noInit", "broadcast", "echoSent", "accept"}
    /\ \A p \in Faulty :
          pc[p] = "noInit"
    /\ recv \in [PROC -> SUBSET Message]
    /\ sent \subseteq { [type |-> "ECHO", sender |-> p] : p \in Correct }

(* -------------------------------------------------------------------------- *)
(*   Fixed configuration constraints                                         *)
(* -------------------------------------------------------------------------- *)

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

(* -------------------------------------------------------------------------- *)
(*   LTL properties                                                          *)
(* -------------------------------------------------------------------------- *)

(* If every correct process starts with the INIT message, eventually all
   correct processes accept. *)
CorrLtl ==
    [] ( ( \A p \in Correct : pc[p] = "broadcast" )
        => <> ( \A p \in Correct : pc[p] = "accept" ) )

(* If any correct process accepts, eventually all correct processes accept. *)
RelayLtl ==
    [] ( ( \E p \in Correct : pc[p] = "accept" )
        => <> ( \A p \in Correct : pc[p] = "accept" ) )

(* If no correct process started with the INIT message, then no correct
   process ever accepts. *)
UnforgLtl ==
    [] ( ( \A p \in Correct : pc[p] # "broadcast" )
        => [] ( \A p \in Correct : pc[p] # "accept" ) )

=============================================================================