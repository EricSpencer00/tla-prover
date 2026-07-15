---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT N, T, F

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
ProcSet == 1..N

ECHO == "ECHO"

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES
    correct,    \* Set of correct processes
    faulty,     \* Set of Byzantine processes
    pc,         \* Control location per process
    rcv,        \* Received messages per process
    sentEchos   \* Set of (sender, type) messages that have been sent

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Msg == [sender : ProcSet, type : {ECHO}]

InitCorrectSet == { p \in ProcSet : p <= N - F }

InitFaultySet  == ProcSet \ InitCorrectSet

PCValues == {"InitNo", "InitYes", "Echoed", "Accepted"}

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ correct = InitCorrectSet
    /\ faulty  = InitFaultySet
    /\ pc = [p \in ProcSet |-> 
                IF p \in correct THEN 
                    IF p \in {1} THEN "InitYes" ELSE "InitNo"
                ELSE "InitNo"]
    /\ rcv = [p \in ProcSet |-> {}]
    /\ sentEchos = {}

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
ReceiveCorrect(p) ==
    /\ p \in correct
    /\ \E new \subseteq sentEchos :
          /\ rcv[p] = rcv[p] \cup new

ByzSend(p) ==
    /\ p \in faulty
    /\ \E new \subseteq { [sender |-> p, type |-> ECHO] } :
          /\ rcv[p] = rcv[p] \cup new

SendEcho(p) ==
    /\ p \in correct
    /\ pc[p] \in {"InitYes", "Echoed", "InitNo"}
    /\ rcv[p] = rcv[p] \cup { [sender |-> p, type |-> ECHO] }
    /\ sentEchos' = sentEchos \cup { [sender |-> p, type |-> ECHO] }

Accept(p) ==
    /\ p \in correct
    /\ pc[p] # "Accepted"
    /\ pc[p]' = "Accepted"

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ \E p \in correct : ReceiveCorrect(p)
    \/ \E p \in faulty  : ByzSend(p)
    \/ \E p \in correct :
        /\ pc[p] = "InitYes"
        /\ SendEcho(p)
        /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    \/ \E p \in correct :
        /\ pc[p] = "InitNo"
        /\ LET echoSenders == { s \in correct : [sender |-> s, type |-> ECHO] \in rcv[p] } IN
           /\ Len(echoSenders) >= N - 2*T
           /\ Len(echoSenders) < N - T
           /\ SendEcho(p)
           /\ pc' = [pc EXCEPT ![p] = "Echoed"]
    \/ \E p \in correct :
        /\ pc[p] \in {"InitNo", "Echoed"}
        /\ LET echoSenders == { s \in correct : [sender |-> s, type |-> ECHO] \in rcv[p] } IN
           /\ Len(echoSenders) >= N - T
           /\ SendEcho(p)
           /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    \/ \E p \in correct :
        /\ pc[p] = "Echoed"
        /\ LET echoSenders == { s \in correct : [sender |-> s, type |-> ECHO] \in rcv[p] } IN
           /\ Len(echoSenders) >= N - T
           /\ Accept(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<correct, faulty, pc, rcv, sentEchos>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK ==
    /\ correct \subseteq ProcSet
    /\ faulty  \subseteq ProcSet
    /\ correct \cup faulty = ProcSet
    /\ correct \cap faulty = {}
    /\ pc \in [ProcSet -> PCValues]
    /\ rcv \in [ProcSet -> SUBSET Msg]
    /\ sentEchos \subseteq Msg

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

(*-----------------------------------------------------------------
  Liveness properties (as invariants for model checking)
-----------------------------------------------------------------*)
CorrLtl == \A p \in correct : pc[p] = "Accepted"
RelayLtl == 
    \A p, q \in correct : (pc[p] = "Accepted") => (pc[q] = "Accepted")
UnforgLtl ==
    \A p \in correct :
        (pc[p] = "Accepted") => 
            \E p0 \in correct : pc[p0] = "InitYes"

=============================================================================