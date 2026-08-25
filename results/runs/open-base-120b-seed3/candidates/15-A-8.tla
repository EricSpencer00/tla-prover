---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F

(* ---------------------------------------------------------------------- *)
(* Process identifiers *)
Proc == 1 .. N

(* ---------------------------------------------------------------------- *)
(* Message definition (only ECHO messages) *)
Message == [type : {"ECHO"}, sender : Proc]

(* ---------------------------------------------------------------------- *)
(* Variables *)
VARIABLES Correct, Faulty, initRecv, echoSent, accepted, recv

vars == <<Correct, Faulty, initRecv, echoSent, accepted, recv>>

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)

EchosFromCorrect == { [type |-> "ECHO", sender |-> q] : q \in echoSent }

ByzEchos == { [type |-> "ECHO", sender |-> b] : b \in Faulty }

AllowedNew(p) == (EchosFromCorrect \cup ByzEchos) \ recv[p]

DistinctSenders(S) == { m.sender : m \in S }

CountDistinctSenders(S) == Cardinality(DistinctSenders(S))

(* ---------------------------------------------------------------------- *)
(* Initialization *)

Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ initRecv \subseteq Correct
    /\ echoSent = {}
    /\ accepted = {}
    /\ recv = [p \in Correct |-> {}]

(* ---------------------------------------------------------------------- *)
(* Receive and act step for a correct process p *)

ReceiveAndAct(p) ==
    /\ p \in Correct
    /\ \E new \subseteq AllowedNew(p) :
        LET newRecv == recv[p] \cup new IN
        LET cnt == CountDistinctSenders(newRecv) IN
        /\ recv' = [recv EXCEPT ![p] = newRecv]
        /\ UNCHANGED <<Correct, Faulty, initRecv>>
        /\ IF p \in initRecv THEN
               /\ echoSent' = echoSent \cup {p}
               /\ accepted' = accepted \cup {p}
           ELSE IF (p \notin echoSent) /\ cnt >= N - 2*T /\ cnt < N - T THEN
               /\ echoSent' = echoSent \cup {p}
               /\ accepted' = accepted
           ELSE IF (p \notin echoSent) /\ cnt >= N - T THEN
               /\ echoSent' = echoSent \cup {p}
               /\ accepted' = accepted \cup {p}
           ELSE IF (p \in echoSent) /\ (p \notin accepted) /\ cnt >= N - T THEN
               /\ echoSent' = echoSent
               /\ accepted' = accepted \cup {p}
           ELSE
               /\ echoSent' = echoSent
               /\ accepted' = accepted

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)

Next ==
    \/ \E p \in Correct : ReceiveAndAct(p)

(* ---------------------------------------------------------------------- *)
(* Specification *)

Spec ==
    Init /\ [][Next]_vars /\ \A p \in Proc : WF_vars(ReceiveAndAct(p))

(* ---------------------------------------------------------------------- *)
(* Type correctness invariant *)

TypeOK ==
    /\ Correct \subseteq Proc
    /\ Faulty = Proc \ Correct
    /\ initRecv \subseteq Correct
    /\ echoSent \subseteq Correct
    /\ accepted \subseteq Correct
    /\ recv \in [Correct -> SUBSET Message]
    /\ \A p \in Correct : recv[p] \subseteq Message
    /\ \A m \in Message : m.type = "ECHO" /\ m.sender \in Proc

(* ---------------------------------------------------------------------- *)
(* Fault constraints invariant *)

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

(* ---------------------------------------------------------------------- *)
(* Liveness properties *)

CorrLtl ==
    ( \A p \in Correct : p \in initRecv ) => <> ( \A p \in Correct : p \in accepted )

RelayLtl ==
    ( \E p \in Correct : p \in accepted ) => <> ( \A p \in Correct : p \in accepted )

UnforgLtl ==
    [] ( initRecv = {} => ( \A p \in Correct : p \notin accepted ) )

=============================================================================