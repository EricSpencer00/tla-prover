---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS N, T, F

(* Derived sets *)
Proc == 1..N
ECHO == "ECHO"

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    correct,          \* set of correct processes
    faulty,           \* set of Byzantine processes
    pc,               \* control location per process
    sent,             \* set of (sender, msg) pairs sent by correct processes
    recv,             \* received messages per process
    accepted          \* set of processes that have accepted

(*-----------------------------------------------------------------
  Control locations
-----------------------------------------------------------------*)
LocInitNo  == "InitNo"
LocInitYes == "InitYes"
LocEcho    == "EchoSent"
LocAccept  == "Accepted"

Locs == {LocInitNo, LocInitYes, LocEcho, LocAccept}

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Msg == [type : {"ECHO"}, sender : Proc]

MessagesFromCorrect == { [type |-> "ECHO", sender |-> p] : p \in correct }
MessagesFromByzantine == { [type |-> "ECHO", sender |-> p] : p \in faulty }

AllPossibleSent == MessagesFromCorrect \cup MessagesFromByzantine

EchoSend(p) == [type |-> "ECHO", sender |-> p]

EchoSendSet == { EchoSend(p) : p \in correct }

DistinctSenders(S) == { m.sender : m \in S }

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ \A p \in Proc :
          pc[p] \in {LocInitNo, LocInitYes}
    /\ pc = [p \in Proc |-> IF p \in correct THEN LocInitNo ELSE LocInitNo]  \* initial state: all in InitNo
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]
    /\ accepted = {}

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
(* 1. Receive new messages *)
Receive(p) ==
    /\ p \in correct
    /\ \E new \subseteq AllPossibleSent :
          /\ new = new \ { m \in recv[p] : TRUE }  \* only messages not yet received
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
          /\ UNCHANGED <<correct, faulty, pc, sent, accepted>>

(* 2. Immediate accept and send ECHO after InitYes *)
InitAcceptAndEcho(p) ==
    /\ p \in correct
    /\ pc[p] = LocInitYes
    /\ pc' = [pc EXCEPT ![p] = LocAccept]
    /\ sent' = sent \cup { EchoSend(p) }
    /\ accepted' = accepted \cup {p}
    /\ UNCHANGED <<correct, faulty, recv>>

(* 3. Send ECHO after receiving >= N-2T but < N-T ECHOs *)
EchoAfterPartial(p) ==
    /\ p \in correct
    /\ pc[p] \in {LocInitNo, LocInitYes}
    /\ \A m \in recv[p] : m.type = "ECHO"
    /\ LET echos == { m \in recv[p] : m.type = "ECHO" } IN
       /\ Cardinality(DistinctSenders(echos)) >= N - 2*T
       /\ Cardinality(DistinctSenders(echos)) < N - T
    /\ pc' = [pc EXCEPT ![p] = LocEcho]
    /\ sent' = sent \cup { EchoSend(p) }
    /\ UNCHANGED <<correct, faulty, recv, accepted>>

(* 4. Send ECHO and accept after receiving >= N-T ECHOs, not yet sent *)
EchoAndAccept(p) ==
    /\ p \in correct
    /\ pc[p] \in {LocInitNo, LocInitYes}
    /\ \A m \in recv[p] : m.type = "ECHO"
    /\ LET echos == { m \in recv[p] : m.type = "ECHO" } IN
       Cardinality(DistinctSenders(echos)) >= N - T
    /\ pc' = [pc EXCEPT ![p] = LocAccept]
    /\ sent' = sent \cup { EchoSend(p) }
    /\ accepted' = accepted \cup {p}
    /\ UNCHANGED <<correct, faulty, recv>>

(* 5. Accept after already sent ECHO and receive >= N-T ECHOs *)
AcceptAfterEcho(p) ==
    /\ p \in correct
    /\ pc[p] = LocEcho
    /\ \A m \in recv[p] : m.type = "ECHO"
    /\ LET echos == { m \in recv[p] : m.type = "ECHO" } IN
       Cardinality(DistinctSenders(echos)) >= N - T
    /\ pc' = [pc EXCEPT ![p] = LocAccept]
    /\ accepted' = accepted \cup {p}
    /\ UNCHANGED <<correct, faulty, sent, recv>>

(* 6. No‑op (stuttering) *)
Stutter ==
    UNCHANGED <<correct, faulty, pc, sent, recv, accepted>>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ \E p \in correct : Receive(p)
    \/ \E p \in correct : InitAcceptAndEcho(p)
    \/ \E p \in correct : EchoAfterPartial(p)
    \/ \E p \in correct : EchoAndAccept(p)
    \/ \E p \in correct : AcceptAfterEcho(p)
    \/ Stutter

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<correct, faulty, pc, sent, recv, accepted>>

(*-----------------------------------------------------------------
  Type correctness invariant
-----------------------------------------------------------------*)
MsgSet == { EchoSend(p) : p \in Proc }

TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ pc \in [Proc -> Locs]
    /\ sent \subseteq MsgSet
    /\ recv \in [Proc -> SUBSET MsgSet]
    /\ accepted \subseteq correct

(*-----------------------------------------------------------------
  Safety invariant: unforgeability / FCConstraints
-----------------------------------------------------------------*)
Unforgeability ==
    /\ \A p \in correct : pc[p] \notin {LocEcho, LocAccept}
    /\ \A p \in correct : accepted[p] = FALSE

FCConstraints == Unforgeability

(*-----------------------------------------------------------------
  Liveness properties (written as state formulas for .cfg)
-----------------------------------------------------------------*)
CorrLtl == \A p \in correct : pc[p] = LocAccept
RelayLtl == \A p \in correct : pc[p] = LocAccept
UnforgLtl == FCConstraints

====