---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

(* ----------------------------------------------------------------------
   Process set and message type
   ---------------------------------------------------------------------- *)
Proc == 1..N
ECHO == "ECHO"

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)
VARIABLES Correct, Faulty, initRecv, pc, recv, sent

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
EchoSet(p) == { s \in Proc : <<s, ECHO>> \in recv[p] }

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ initRecv \subseteq Correct
  /\ pc \in [Proc -> {"NoInit", "EchoSent", "Accepted"}]
  /\ recv \in [Proc -> SUBSET (Proc \X {ECHO})]
  /\ sent \subseteq Proc \X {ECHO}

(* ----------------------------------------------------------------------
   Fault‑tolerance constraints
   ---------------------------------------------------------------------- *)
FCConstraints == N > 3 * T /\ T >= F

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ initRecv \subseteq Correct
  /\ pc = [p \in Proc |-> "NoInit"]
  /\ recv = [p \in Proc |-> {}]
  /\ sent = {}

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

(* A correct process may receive any set of ECHO messages (including
   those forged by Byzantine processes). *)
Receive(p, new) ==
  /\ p \in Correct
  /\ new \subseteq Proc \X {ECHO}
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
  /\ UNCHANGED <<Correct, Faulty, initRecv, pc, sent>>

(* Sending an ECHO.  The process may also accept immediately
   depending on the number of distinct ECHO messages it has seen. *)
SendEcho(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ (p \in initRecv \/ Cardinality(EchoSet(p)) >= N - 2 * T)
  /\ ~<<p, ECHO>> \in sent
  /\ sent' = sent \cup {<<p, ECHO>>}
  /\ pc' = [pc EXCEPT ![p] =
        IF (p \in initRecv \/ Cardinality(EchoSet(p)) >= N - T)
           THEN "Accepted"
           ELSE "EchoSent"]
  /\ UNCHANGED <<Correct, Faulty, initRecv, recv>>

(* Accepting the broadcast. *)
Accept(p) ==
  /\ p \in Correct
  /\ pc[p] # "Accepted"
  /\ (p \in initRecv
      \/ Cardinality(EchoSet(p)) >= N - T
      \/ (pc[p] = "EchoSent" /\ Cardinality(EchoSet(p)) >= N - T))
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, initRecv, recv, sent>>

Next ==
  \/ \E p \in Proc : \E new \subseteq Proc \X {ECHO} : Receive(p, new)
  \/ \E p \in Proc : SendEcho(p)
  \/ \E p \in Proc : Accept(p)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<Correct, Faulty, initRecv, pc, recv, sent>> /\ WF_vars(Next)

(* ----------------------------------------------------------------------
   LTL properties
   ---------------------------------------------------------------------- *)

(* If every correct process initially receives the INIT message,
   eventually all correct processes accept. *)
CorrLtl == (initRecv = Correct) => <> ( \A p \in Correct : pc[p] = "Accepted" )

(* If any correct process accepts, eventually all correct processes accept. *)
RelayLtl == [] ( ( \E p \in Correct : pc[p] = "Accepted" ) => <> ( \A p \in Correct : pc[p] = "Accepted" ) )

(* If no correct process receives the INIT message, no correct process ever accepts. *)
UnforgLtl == (initRecv = {}) => [] ( \A p \in Correct : pc[p] # "Accepted" )

====