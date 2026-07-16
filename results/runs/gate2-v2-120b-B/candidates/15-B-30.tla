---- MODULE bcastByz ----
EXTENDS Naturals, 
        FiniteSets,
        Functions,
        FunctionTheorems, 
        FiniteSetTheorems,
        NaturalsInduction,
        SequenceTheorems,
        TLAPS
        
CONSTANTS N, T, F

VARIABLE Corr           (* the correct processes *)
VARIABLE Faulty         (* the faulty processes *)

VARIABLE pc             (* the control state of each process *)
VARIABLE rcvd           (* the messages received by each process *)
VARIABLE sent           (* the messages sent by all correct processes *)

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N          (* all processes, including the faulty ones    *)
M == {"ECHO"}
ByzMsgs == Faulty \X M
                            
vars == << pc, rcvd, sent, Corr, Faulty >>

(* Initial state: no messages sent, each process is either V0 or V1, all processes are partitioned
   into Corr and Faulty with the required cardinalities. *)
Init == 
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* Special initial state for the unforgeability property: all processes start in V0. *)
InitNoBcast == 
  /\ Init
  /\ pc = [ i \in Proc |-> "V0" ]

(* Receive a (possibly empty) set of new messages; the set may also contain Byzantine messages
   if includeByz is TRUE. *)
Receive(self, includeByz) ==
  \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[i] \cup newMessages ELSE rcvd[i] ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)    == Receive(self, TRUE)

(* A correct process that is in state V1 sends an ECHO message. *)
UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

(* A correct process that has already left the initial states and has received enough ECHO
   messages from distinct processes (but not too many) sends an ECHO message. *)
UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd[self]) >= N - 2*T
  /\ Cardinality(rcvd[self]) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

(* A process in an initial state that receives ECHO from at least N‑T distinct processes
   accepts and also sends an ECHO. *)
UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"}
  /\ Cardinality(rcvd[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

(* A process that has already sent an ECHO (state SE) and receives enough ECHO messages
   accepts without sending another message. *)
UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ UNCHANGED << sent, Corr, Faulty, rcvd >>

(* A single step of a correct process: receive (possibly Byzantine) messages and then
   optionally execute one of the protocol actions. *)
Step(self) == 
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

(* Next allows any correct process to take a step, or stutter. *)
Next ==
  \/ \E self \in Corr: Step(self)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

(* Safety property: no correct process ever reaches the accepted state. *)
Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

(* Safety property is the invariant we will check. *)
Inv == 
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ TypeOK

(* Helper definition for the type invariant. *)
TypeOK == 
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]          
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \times M     
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

=============================================================================