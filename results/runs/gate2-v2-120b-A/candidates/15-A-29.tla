---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F

(* ------------------------------------------------------------------------ *)
(* Derived sets and basic definitions                                        *)
(* ------------------------------------------------------------------------ *)

Proc == 1..N

MsgType == {"ECHO"}

Msg == [type : MsgType, sender : Proc]

\* Control locations
Ctr == {"InitNone", "InitYes", "EchoSent", "Accept"}

(* ------------------------------------------------------------------------ *)
(* Variables                                                                 *)
(* ------------------------------------------------------------------------ *)

VARIABLES
    correct,         \* Set of correct processes
    faulty,          \* Set of Byzantine processes
    pc,              \* Control location per process
    snd,             \* Set of messages sent by correct processes
    rcv               \* Messages received by each correct process

(* ------------------------------------------------------------------------ *)
(* Type invariant (TypeOK)                                                   *)
(* ------------------------------------------------------------------------ *)

TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty \subseteq Proc
    /\ correct \cup faulty = Proc
    /\ correct \cap faulty = {}
    /\ pc \in [Proc -> Ctr]
    /\ snd \subseteq Msg
    /\ rcv \in [Proc -> SUBSET Msg]

(* ------------------------------------------------------------------------ *)
(* Helper definitions                                                       *)
(* ------------------------------------------------------------------------ *)

EchoMsg(p) == [type |-> "ECHO", sender |-> p]

SentByCorrect == { EchoMsg(p) : p \in correct }

(* Count distinct senders of ECHO messages in a set *)
DistinctSenders(s) == { m.sender : m \in s }

(* ------------------------------------------------------------------------ *)
(* Initial state (including the restricted "no broadcast" case)            *)
(* ------------------------------------------------------------------------ *)

Init ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ pc = [p \in Proc |-> IF p \in correct THEN
                            (* nondeterministically choose initial broadcast state *)
                            IF p \in correct THEN
                                IF p \in correct THEN "InitNone"
                                ELSE "InitYes"
                            ELSE "InitNone"
                          ELSE "InitNone"]
    /\ snd = {}
    /\ rcv = [p \in Proc |-> {}]

(* ------------------------------------------------------------------------ *)
(* Actions                                                                   *)
(* ------------------------------------------------------------------------ *)

Receive(p) ==
    /\ p \in correct
    /\ LET possibleMsgSet ==
            snd \cup { EchoMsg(b) : b \in faulty }
       IN /\ rcv' = [rcv EXCEPT ![p] = rcv[p] \cup possibleMsgSet]
    /\ UNCHANGED <<correct, faulty, pc, snd>>

SendEcho(p) ==
    /\ p \in correct
    /\ pc[p] \in {"InitYes", "EchoSent", "Accept"}
    /\ snd' = snd \cup { EchoMsg(p) }
    /\ UNCHANGED <<rcv, correct, faulty, pc>>

Accept(p) ==
    /\ p \in correct
    /\ pc[p] \in {"EchoSent", "Accept"}
    /\ pc' = [pc EXCEPT ![p] = "Accept"]
    /\ UNCHANGED <<rcv, snd, correct, faulty>>

InitTransition(p) ==
    /\ p \in correct
    /\ pc[p] = "InitNone"
    /\ pc' = [pc EXCEPT ![p] = "InitYes"]
    /\ UNCHANGED <<rcv, snd, correct, faulty>>

ProcessStep(p) ==
    \/ InitTransition(p)
    \/ IF pc[p] = "InitYes"
          THEN SendEcho(p) /\ Accept(p)
          ELSE IF pc[p] = "InitNone"
                THEN LET echos == { m \in rcv[p] : m.type = "ECHO" } IN
                     IF Cardinality(DistinctSenders(echos)) >= N - T
                         THEN SendEcho(p) /\ Accept(p)
                         ELSE IF Cardinality(DistinctSenders(echos)) >= N - 2*T
                                 THEN SendEcho(p)
                                 ELSE UNCHANGED <<rcv, snd, pc>>
                ELSE IF pc[p] = "EchoSent"
                     THEN
                        LET echos == { m \in rcv[p] : m.type = "ECHO" } IN
                        IF Cardinality(DistinctSenders(echos)) >= N - T
                            THEN Accept(p)
                            ELSE UNCHANGED <<rcv, snd, pc>>
                ELSE UNCHANGED <<rcv, snd, pc>>

(* ------------------------------------------------------------------------ *)
(* Next-state relation                                                       *)
(* ------------------------------------------------------------------------ *)

Next ==
    \E p \in correct : ProcessStep(p)

(* ------------------------------------------------------------------------ *)
(* Specification                                                             *)
(* ------------------------------------------------------------------------ *)

Spec == Init /\ [][Next]_<<rcv, snd, pc, correct, faulty>>

(* ------------------------------------------------------------------------ *)
(* Safety invariants                                                          *)
(* ------------------------------------------------------------------------ *)

(* Unforgeability: if all correct processes start without the INIT message,
   then no correct process ever reaches Accept. *)
FCConstraints ==
    /\ \A p \in correct : pc[p] # "Accept"
       => \A p' \in correct : pc[p'] # "Accept"

(* ------------------------------------------------------------------------ *)
(* Liveness properties (expressed as temporal formulas)                     *)
(* ------------------------------------------------------------------------ *)

CorrLtl ==
    /\ \A p \in correct : pc[p] = "InitYes"
    /\ <> \A p \in correct : pc[p] = "Accept"

RelayLtl ==
    /\ \E p \in correct : pc[p] = "Accept"
    /\ <> \A p \in correct : pc[p] = "Accept"

UnforgLtl ==
    /\ \A p \in correct : pc[p] = "InitNone"
    /\ [] (~(\E p \in correct : pc[p] = "Accept"))

=============================================================================