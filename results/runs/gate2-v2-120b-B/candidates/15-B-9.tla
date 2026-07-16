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

VARIABLE Corr           
VARIABLE Faulty         
VARIABLE pc             
VARIABLE rcvd           
VARIABLE sent           

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N          
M == { "ECHO" }          
ByzMsgs == Faulty \X M   

vars == << pc, rcvd, sent, Corr, Faulty >>

(* Initial state: no messages have been sent, all processes start in V0,
   and the sets of correct and faulty processes are chosen nondeterministically
   but satisfy the cardinality constraints. *)
Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* Receive a (possibly empty) set of new messages from any sender. *)
Receive(self, includeByz) ==
  \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[i] \cup newMessages ELSE rcvd[i] ]

(* A correct process that is in state V1 sends an ECHO message. *)
UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

(* A correct process that has already sent ECHO and has received enough
   distinct ECHO messages from other processes sends another ECHO. *)
UponNonFaulty(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd[self]) >= N - 2*T
  /\ Cardinality(rcvd[self]) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

(* A correct process that receives ECHO from at least N‑T distinct processes
   accepts and also sends an ECHO (if it has not sent one before). *)
UponAccept(self) ==
  /\ pc[self] \in {"V0", "V1", "SE"}
  /\ Cardinality(rcvd[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

(* A step of a correct process: receive messages, then possibly take one of
   the actions defined above.  The order of actions is irrelevant for safety. *)
Step(self) ==
  /\ Receive(self, TRUE)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAccept(self)

Next ==
  \/ \E self \in Corr: Step(self)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

(* Unforgeability: a correct process never reaches the accepted state. *)
Unforg == \A i \in Corr : pc[i] # "AC"

=============================================================================