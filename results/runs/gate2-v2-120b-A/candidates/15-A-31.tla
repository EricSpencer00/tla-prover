---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

(* ----------------------------------------------------------------------
   Derived constants
   ---------------------------------------------------------------------- *)
\* Number of correct processes
CORRECT_COUNT == N - F

(* ----------------------------------------------------------------------
   Process sets
   ---------------------------------------------------------------------- *)
Variable correct, faulty

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
Variable pc          \* control location: "Init", "EchSent", "Accepted"
Variable sent        \* set of sent ECHO messages (just sender ids)
Variable recv        \* mapping: process -> set of received ECHO senders

(* ----------------------------------------------------------------------
   Message type (only ECHO needed)
   ---------------------------------------------------------------------- *)
ECHO == "ECHO"

(* ----------------------------------------------------------------------
   Init predicate
   ---------------------------------------------------------------------- *)
Init ==
    /\ correct \in SUBSET 1..N
    /\ Cardinality(correct) = CORRECT_COUNT
    /\ faulty = 1..N \ correct
    /\ pc = [p \in 1..N |-> 
                IF p \in correct THEN 
                    IF p \in correct \ {c \in correct : c \in {}} THEN "Init"
                    ELSE "Init" \* all start in the same initial state; the distinction
                                 \* between "received INIT" and "not received INIT" is modeled
                                 \* by nondeterministic choice in the first step.
                ELSE "Init"]
    /\ sent = {}
    /\ recv = [p \in 1..N |-> {}]

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
DistinctSenders(s) == { s }

Echokey(p) == <<p, ECHO>>

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

(* Correct process receives a set of ECHO messages from any senders *)
Receive(p) ==
    /\ p \in correct
    /\ \E new \subseteq (sent \cup {b \in faulty : TRUE}) :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
        /\ UNCHANGED <<pc, sent, correct, faulty>>

(* A correct process that has received INIT (modeled as being in state "Init") 
   immediately sends its own ECHO and accepts *)
InitEchoAndAccept(p) ==
    /\ p \in correct
    /\ pc[p] = "Init"
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup {p}
    /\ UNCHANGED <<recv, correct, faulty>>

(* A correct process that has not yet sent ECHO and receives at least N-2T distinct
   ECHO messages (but fewer than N-T) sends its own ECHO but does not yet accept *)
EchoWhenThresholdLow(p) ==
    /\ p \in correct
    /\ pc[p] = "Init"
    /\ LET r == recv[p] IN
        /\ Cardinality(r) >= N - 2 * T
        /\ Cardinality(r) < N - T
    /\ pc' = [pc EXCEPT ![p] = "EchSent"]
    /\ sent' = sent \cup {p}
    /\ UNCHANGED <<recv, correct, faulty>>

(* A correct process that has not yet sent ECHO and receives at least N-T distinct
   ECHO messages sends its own ECHO and accepts *)
EchoWhenThresholdHigh(p) ==
    /\ p \in correct
    /\ pc[p] = "Init"
    /\ Cardinality(recv[p]) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup {p}
    /\ UNCHANGED <<recv, correct, faulty>>

(* A correct process that already sent ECHO accepts upon receiving N-T distinct ECHOs *)
AcceptAfterEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "EchSent"
    /\ Cardinality(recv[p]) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<sent, recv, correct, faulty>>

(* Byzantine processes may arbitrarily add fake ECHO messages to the global sent set *)
ByzantineSend ==
    /\ \E b \in faulty :
        /\ sent' = sent \cup {b}
    /\ UNCHANGED <<pc, recv, correct, faulty>>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ \E p \in correct : Receive(p)
    \/ \E p \in correct : InitEchoAndAccept(p)
    \/ \E p \in correct : EchoWhenThresholdLow(p)
    \/ \E p \in correct : EchoWhenThresholdHigh(p)
    \/ \E p \in correct : AcceptAfterEcho(p)
    \/ ByzantineSend

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<pc, sent, recv, correct, faulty>>

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ correct \subseteq 1..N
    /\ faulty = 1..N \ correct
    /\ pc \in [1..N -> {"Init", "EchSent", "Accepted"}]
    /\ sent \subseteq correct
    /\ \A p \in 1..N: recv[p] \subseteq (sent \cup faulty)

(* ----------------------------------------------------------------------
   Safety invariant (FCConstraints) – no forged acceptance when
   no correct process ever receives INIT (i.e., all start without it)
   Here we model that by requiring that initially no correct process is
   in the "Accepted" state, and we assert that this never happens.
   ---------------------------------------------------------------------- *)
FCConstraints ==
    ~(\E p \in correct : pc[p] = "Accepted")

(* ----------------------------------------------------------------------
   Safety property: Unforgeability expressed as an LTL property
   ---------------------------------------------------------------------- *)
UnforgLtl == [] ( (\A p \in correct : pc[p] # "Accepted") => [] (\A p \in correct : pc[p] # "Accepted") )

(* ----------------------------------------------------------------------
   Liveness properties
   ---------------------------------------------------------------------- *)

(* CorrLtl: If every correct process starts in the "Init" state (interpreted as
   having received the broadcaster's INIT), then eventually all correct
   processes are in "Accepted". *)
CorrLtl == [] ( (\A p \in correct : pc[p] = "Init") => <> (\A p \in correct : pc[p] = "Accepted") )

(* RelayLtl: If any correct process ever reaches "Accepted", then eventually
   all correct processes reach "Accepted". *)
RelayLtl == [] ( (\E p \in correct : pc[p] = "Accepted") => <> (\A p \in correct : pc[p] = "Accepted") )

====