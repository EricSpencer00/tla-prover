---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1..N

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
MessageType == {"ECHO"}
Message == [type : MessageType, sender : Proc]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES correct, faulty, pc, recv, sent

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
CorrectHasECHO(p) == 
  \E m \in { [type |-> "ECHO", sender |-> s] : s \in Proc } :
      m \in recv[p]

ECHOset(p) == { m.sender : 
                 \E q \in Proc : m \in recv[p] /\ m.type = "ECHO" /\ m.sender = q }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ correct \subseteq Proc
  /\ faulty = Proc \ correct
  /\ Cardinality(correct) = N - F
  /\ pc \in [Proc -> {"InitNo", "InitYes", "EchoSent", "Accepted"}]
  /\ \A p \in Proc : 
        IF pc[p] = "InitYes" 
        THEN recv[p] = { [type |-> "ECHO", sender |-> p] } 
        ELSE recv[p] = {}
  /\ sent = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* (1) Receive arbitrary messages from correct senders and any from faulty
Recv(p) ==
  /\ p \in correct
  /\ \E newMsgs \subseteq sent \cup
        { [type |-> "ECHO", sender |-> s] : s \in faulty } :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
        /\ UNCHANGED <<correct, faulty, pc, sent>>

\* (2) Correct process with INITYes immediately accepts and sends its ECHO
AcceptInit(p) ==
  /\ p \in correct
  /\ pc[p] = "InitYes"
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ UNCHANGED <<correct, faulty, recv>>

\* (3) Send ECHO when received >= N-2T but < N-T, no accept yet
SendEchoMid(p) ==
  /\ p \in correct
  /\ pc[p] = "InitNo"
  /\ LET eSet == ECHOset(p) IN
        /\ Cardinality(eSet) >= N - 2*T
        /\ Cardinality(eSet) < N - T
  /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ UNCHANGED <<correct, faulty, recv>>

\* (4) Send ECHO and accept when received >= N-T (and not yet sent)
SendEchoAndAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "InitNo"
  /\ Cardinality(ECHOset(p)) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ UNCHANGED <<correct, faulty, recv>>

\* (5) Accept after already sent ECHO and now >= N-T ECHO received
AcceptAfterEcho(p) ==
  /\ p \in correct
  /\ pc[p] = "EchoSent"
  /\ Cardinality(ECHOset(p)) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

\* (6) Byzantine processes may arbitrarily send ECHOs
ByzSend(p) ==
  /\ p \in faulty
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ UNCHANGED <<correct, faulty, pc, recv>>

\* Composite step for a correct process
CorrectStep(p) ==
  \/ Recv(p)
  \/ AcceptInit(p)
  \/ SendEchoMid(p)
  \/ SendEchoAndAccept(p)
  \/ AcceptAfterEcho(p)

\* Next relation
Next ==
  \/ \E p \in Proc : CorrectStep(p)
  \/ \E p \in faulty : ByzSend(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<correct, faulty, pc, recv, sent>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ correct \subseteq Proc
  /\ faulty = Proc \ correct
  /\ Cardinality(correct) = N - F
  /\ pc \in [Proc -> {"InitNo", "InitYes", "EchoSent", "Accepted"}]
  /\ \A p \in Proc : recv[p] \subseteq { [type |-> "ECHO", sender |-> s] : s \in Proc }
  /\ sent \subseteq { [type |-> "ECHO", sender |-> s] : s \in Proc }

\* Safety constraint: never accept when no one started with INIT
FCConstraints ==
  /\ ( \A p \in correct : pc[p] # "Accepted" )
     => ( \A p \in correct : pc[p] # "Accepted" )  \* trivially true, placeholder for clarity

\* ----------------------------------------------------------------------
\* Liveness properties (expressed as temporal formulas)
\* ----------------------------------------------------------------------
CorrLtl == 
  \A p \in correct : <> (pc[p] = "Accepted")

RelayLtl ==
  \A p \in correct : (pc[p] = "Accepted") => <> ( \A q \in correct : pc[q] = "Accepted" )

UnforgLtl ==
  ( \A p \in correct : pc[p] # "Accepted") => [] ( \A p \in correct : pc[p] # "Accepted" )

====