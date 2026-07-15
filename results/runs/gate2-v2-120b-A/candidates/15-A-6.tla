---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*--------------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
--------------------------------------------------------------------*)
CONSTANT N \* number of processes
CONSTANT T \* Byzantine tolerance
CONSTANT F \* number of faulty processes (F <= T)

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
Proc == 1..N

ECHO == "ECHO"

Msg == [type : {"ECHO"} , sender : Proc]

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES
    correct,          \* set of correct processes
    faulty,           \* set of Byzantine processes
    pc,               \* control location for each process
    received,         \* set of messages received by each process
    sent               \* set of ECHO messages sent by correct processes

(*--------------------------------------------------------------------
  Control locations
--------------------------------------------------------------------*)
Aliases == {"Init", "NonInit"}
SentEcho == {"SentEcho", "NoEcho"}
Accepted == {"Accepted", "NotAccepted"}

pcInit(p) == pc[p][1]
pcSent(p) == pc[p][2]
pcAcc(p) == pc[p][3]

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
InitSets ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ Cardinality(faulty) = F

InitPC(correctInit) ==
    [p \in Proc |-> << IF p \in correctInit THEN "Init" ELSE "NonInit",
                    "NoEcho",
                    "NotAccepted" >>]

InitReceived == [p \in Proc |-> {}]

InitSent == {}

Init ==
    /\ InitSets
    /\ pc = InitPC({})
    /\ received = InitReceived
    /\ sent = InitSent

(*--------------------------------------------------------------------
  Send ECHO action for a correct process p
--------------------------------------------------------------------*)
SendEcho(p) ==
    /\ p \in correct
    /\ pcSent(p) = "NoEcho"
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
    /\ pc' = [pc EXCEPT ![p][2] = "SentEcho"]
    /\ UNCHANGED << correct, faulty, received >>

(*--------------------------------------------------------------------
  Receive messages action for a correct process p
--------------------------------------------------------------------*)
Receive(p) ==
    /\ p \in correct
    /\ LET
        possible == sent
        newMsgs == { m \in possible : m \notin received[p] }
        newSet == CHOOSE s \in SUBSET(newMsgs) : TRUE
      IN
        /\ received' = [received EXCEPT ![p] = received[p] \cup newSet]
        /\ UNCHANGED << correct, faulty, pc, sent >>

(*--------------------------------------------------------------------
  Accept action for a correct process p
--------------------------------------------------------------------*)
Accept(p) ==
    /\ p \in correct
    /\ pcAcc(p) = "NotAccepted"
    /\ pc' = [pc EXCEPT ![p][3] = "Accepted"]
    /\ UNCHANGED << correct, faulty, received, sent >>

(*--------------------------------------------------------------------
  Combined step for a correct process p
--------------------------------------------------------------------*)
CorrectStep(p) ==
    \/ SendEcho(p)
    \/ Accept(p)
    \/ Receive(p)

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \E p \in Proc : CorrectStep(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<< pc, received, sent >>

(*--------------------------------------------------------------------
  Type correctness invariant (TypeOK)
--------------------------------------------------------------------*)
TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ pc \in [Proc -> Seq(1..3, { "Init", "NonInit", "NoEcho",
                                   "SentEcho", "Accepted", "NotAccepted" })]
    /\ received \in [Proc -> SUBSET Msg]
    /\ sent \subseteq { [type |-> "ECHO", sender |-> p] : p \in correct }

(*--------------------------------------------------------------------
  Faulty constraints invariant (FCConstraints)
--------------------------------------------------------------------*)
FCConstraints ==
    /\ Cardinality(correct) = N - F
    /\ Cardinality(faulty) = F
    /\ N > 3 * T
    /\ T >= F

(*--------------------------------------------------------------------
  Safety property: Unforgeability (no acceptance without init)
--------------------------------------------------------------------*)
NoBroadcastInit ==
    \A p \in correct : pcInit(p) = "NonInit"

Unforg == []( \/ ~NoBroadcastInit \/ ~[] (pcAcc(p) = "Accepted") )

UnforgLtl == Unforg

(*--------------------------------------------------------------------
  Liveness property: Correctness (if all init, eventually all accept)
--------------------------------------------------------------------*)
AllInit ==
    \A p \in correct : pcInit(p) = "Init"

AllAccept ==
    \A p \in correct : pcAcc(p) = "Accepted"

CorrLtl == []( AllInit => <> AllAccept )

(*--------------------------------------------------------------------
  Liveness property: Relay (if any accept, eventually all accept)
--------------------------------------------------------------------*)
AnyAccept == \E p \in correct : pcAcc(p) = "Accepted"
RelayLtl == []( AnyAccept => <> AllAccept )

====