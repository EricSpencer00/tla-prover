---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process identifiers
\* ----------------------------------------------------------------------
Proc == 1..N

\* ----------------------------------------------------------------------
\* Message definition (only ECHO messages are modeled)
\* ----------------------------------------------------------------------
Message == [type : {"ECHO"}, from : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, recv, sent

vars == <<Correct, Faulty, pc, recv, sent>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
InitSet == {p \in Proc : pc[p] = "Init"}
NoInitSet == {p \in Proc : pc[p] = "NoInit"}
EchoSentSet == {p \in Proc : pc[p] = "EchoSent"}
AcceptedSet == {p \in Proc : pc[p] = "Accepted"}

EchoSendMsg(p) == [type |-> "ECHO", from |-> p]

EchoSenders(p) == { m.from : m \in recv[p] /\ m.type = "ECHO" }

EchoCount(p) == Cardinality(EchoSenders(p))

NMinus2T == N - 2 * T
NMinusT  == N - T

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Faulty = Proc \ Correct
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]
  /\ pc   = [p \in Proc |-> 
              IF p \in Correct 
                 THEN IF RandomInit(p) THEN "Init" ELSE "NoInit"
                 ELSE "NoInit"]
  /\ \* RandomInit(p) nondeterministically decides whether p
     \* starts with the INIT message (only for correct processes)
     \* It is defined as a Boolean constant (to be instantiated by TLC)
     TRUE

\* A Boolean constant used to choose the initial broadcast state.
\* For the unrestricted model it may be set arbitrarily per process;
\* for the restricted “no‑broadcast” model it must be FALSE for all.
RandomInit(p) == InitChoice[p]
\* (InitChoice is a constant mapping each process to a Boolean; TLC
\*  will assign values consistent with the desired initial condition.)

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Receive arbitrary new messages (from correct senders or any
\*    possible Byzantine messages)
Receive(p) ==
  /\ p \in Correct
  /\ LET
        PossibleByz == { [type |-> "ECHO", from |-> b] :
                          b \in Faulty }
        AllMsgs    == sent \cup PossibleByz
        NewMsgs    == AllMsgs \ recv[p]
        chosen     \in SUBSET NewMsgs
     IN
        /\ chosen # {}
        /\ recv' = [recv EXCEPT ![p] = @ \cup chosen]
        /\ UNCHANGED <<Correct, Faulty, pc, sent>>
  /\ UNCHANGED <<Correct, Faulty, pc, sent>>
  /\ UNCHANGED <<Correct, Faulty, pc, sent>> \* (redundant for clarity)

\* 2. Immediate accept and send ECHO after having INIT
InitAcceptSend(p) ==
  /\ p \in Correct
  /\ pc[p] = "Init"
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ sent' = sent \cup { EchoSendMsg(p) }
  /\ UNCHANGED <<Correct, Faulty, recv>>

\* 3. Send ECHO (but not yet accept) when receiving >= N-2T and < N-T ECHOs
SendEchoOnly(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ EchoCount(p) >= NMinus2T
  /\ EchoCount(p) <  NMinusT
  /\ pc'   = [pc EXCEPT ![p] = "EchoSent"]
  /\ sent' = sent \cup { EchoSendMsg(p) }
  /\ UNCHANGED <<Correct, Faulty, recv>>

\* 4. Send ECHO and accept when receiving >= N-T ECHOs (no prior ECHO sent)
SendEchoAndAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ EchoCount(p) >= NMinusT
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ sent' = sent \cup { EchoSendMsg(p) }
  /\ UNCHANGED <<Correct, Faulty, recv>>

\* 5. Accept after having already sent ECHO and now receiving >= N-T ECHOs
AcceptAfterEcho(p) ==
  /\ p \in Correct
  /\ pc[p] = "EchoSent"
  /\ EchoCount(p) >= NMinusT
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, recv, sent>>

\* The set of all possible steps for a correct process
Step(p) ==
    \/ Receive(p)
    \/ InitAcceptSend(p)
    \/ SendEchoOnly(p)
    \/ SendEchoAndAccept(p)
    \/ AcceptAfterEcho(p)

\* Next is the disjunction of any single correct process taking a step
Next ==
  \E p \in Correct : Step(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_vars
  /\ WF_vars(\E p \in Correct : Receive(p) \/ InitAcceptSend(p) \/ SendEchoOnly(p) \/ SendEchoAndAccept(p) \/ AcceptAfterEcho(p))

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Faulty = Proc \ Correct
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F
  /\ pc \in [Proc -> {"NoInit","Init","EchoSent","Accepted"}]
  /\ recv \in [Proc -> SUBSET Message]
  /\ sent \in SUBSET Message

\* ----------------------------------------------------------------------
\* Fixed‑parameter constraints
\* ----------------------------------------------------------------------
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl ==
  ( \A p \in Correct : pc[p] = "Init" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

RelayLtl ==
  ( \E p \in Correct : pc[p] = "Accepted" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

UnforgLtl ==
  ( \A p \in Correct : pc[p] = "NoInit" ) => [] ( \A p \in Correct : pc[p] # "Accepted" )

=============================================================================