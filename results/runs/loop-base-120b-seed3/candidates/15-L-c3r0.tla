---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

(* ----------------------------------------------------------------------
   Process universe
   ---------------------------------------------------------------------- *)
Proc == 1..N

(* ----------------------------------------------------------------------
   Thresholds
   ---------------------------------------------------------------------- *)
NMinus2T == N - 2 * T
NMinusT  == N - T

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)
VARIABLES Correct, Faulty, pc, recvd, Sent

vars == <<Correct, Faulty, pc, recvd, Sent>>

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
\* control locations
InitRecv == "InitRecv"
InitNot  == "InitNot"
EchoSent == "EchoSent"
Accepted == "Accepted"

AllCorrect == Correct
AllAccepted == \A p \in Correct : pc[p] = Accepted
AllInitRecv == \A p \in Correct : pc[p] = InitRecv
AllInitNot  == \A p \in Correct : pc[p] = InitNot
ExistsAccepted == \E p \in Correct : pc[p] = Accepted

EchoCount(p) == Cardinality(recvd[p])

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {InitRecv, InitNot, EchoSent, Accepted}]
  /\ \A p \in Proc :
        IF p \in Correct THEN pc[p] \in {InitRecv, InitNot}
        ELSE pc[p] = InitNot
  /\ recvd = [p \in Proc |-> {}]
  /\ Sent = {}

(* ----------------------------------------------------------------------
   Receive action (a correct process may receive any subset of messages
   that could have been sent by correct processes together with arbitrary
   messages from Byzantine processes)
   ---------------------------------------------------------------------- *)
Receive(p) ==
  /\ p \in Correct
  /\ LET possible == Sent \cup Faulty
         new      == SUBSET possible
     IN
        recvd' = [recvd EXCEPT ![p] = recvd[p] \cup new]
  /\ UNCHANGED <<Correct, Faulty, pc, Sent>>

(* ----------------------------------------------------------------------
   Echo/Accept step for a correct process
   ---------------------------------------------------------------------- *)
EchoStep(p) ==
  /\ p \in Correct
  /\ LET cnt == EchoCount(p) IN
     \/ /\ pc[p] = InitRecv
        /\ pc' = [pc EXCEPT ![p] = Accepted]
        /\ Sent' = Sent \cup {p}
     \/ /\ pc[p] = InitNot /\ cnt >= NMinusT
        /\ pc' = [pc EXCEPT ![p] = Accepted]
        /\ Sent' = Sent \cup {p}
     \/ /\ pc[p] = InitNot /\ cnt >= NMinus2T /\ cnt < NMinusT
        /\ pc' = [pc EXCEPT ![p] = EchoSent]
        /\ Sent' = Sent \cup {p}
     \/ /\ pc[p] = EchoSent /\ cnt >= NMinusT
        /\ pc' = [pc EXCEPT ![p] = Accepted]
        /\ UNCHANGED Sent
  /\ UNCHANGED <<Correct, Faulty, recvd>>

(* ----------------------------------------------------------------------
   Combined action for a correct process
   ---------------------------------------------------------------------- *)
Action ==
  \E p \in Correct : Receive(p) \/ EchoStep(p)

Next == Action

(* ----------------------------------------------------------------------
   Specification (with weak fairness on Action)
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Action)

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {InitRecv, InitNot, EchoSent, Accepted}]
  /\ recvd \in [Proc -> SUBSET Proc]
  /\ Sent \subseteq Correct

(* ----------------------------------------------------------------------
   Fault‑constraint invariant (model parameters)
   ---------------------------------------------------------------------- *)
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

(* ----------------------------------------------------------------------
   LTL properties
   ---------------------------------------------------------------------- *)
CorrLtl == [] (AllInitRecv => <> AllAccepted)

RelayLtl == [] (ExistsAccepted => <> AllAccepted)

UnforgLtl == [] (AllInitNot => ~<> ExistsAccepted)

=============================================================================