---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N, T, F

(* ---------------------------------------------------------------------- *)
(* Types and derived constants                                            *)
(* ---------------------------------------------------------------------- *)

VARIABLES correct, faulty, pc, sent, recv

(* ---------------------------------------------------------------------- *)
(* Message definition                                                     *)
(* ---------------------------------------------------------------------- *)

Message == {"ECHO"}

(* ---------------------------------------------------------------------- *)
(* Helper definitions                                                    *)
(* ---------------------------------------------------------------------- *)

IDs == 1..N

SenderSet(m) == 
    IF m = "ECHO" THEN IDs ELSE {}

ReceivedEchos(p) == 
    { s \in IDs : <<s, "ECHO">> \in recv[p] }

EchosCount(p) == Cardinality(ReceivedEchos(p))

CanAccept(p) == 
    (pc[p] = "InitBroadcast") \/ (pc[p] = "InitNoBroadcast" /\ EchosCount(p) >= N - T) \/
    (pc[p] = "EchoSent" /\ EchosCount(p) >= N - T)

CanEcho(p) == 
    (pc[p] = "InitNoBroadcast" /\ N - 2*T <= EchosCount(p) /\ EchosCount(p) < N - T) \/
    (pc[p] = "InitNoBroadcast" /\ EchosCount(p) >= N - T) \/
    (pc[p] = "EchoSent" /\ EchosCount(p) >= N - T)

(* ---------------------------------------------------------------------- *)
(* Initial state                                                         *)
(* ---------------------------------------------------------------------- *)

Init ==
    /\ correct \subseteq IDs
    /\ Cardinality(correct) = N - F
    /\ faulty = IDs \ correct
    /\ pc = [p \in IDs |-> 
            IF p \in correct THEN 
                IF "INIT" \in {"INIT"} THEN "InitBroadcast" ELSE "InitNoBroadcast"
            ELSE "Bad"]
    /\ sent = {}
    /\ recv = [p \in IDs |-> {}]

(* ---------------------------------------------------------------------- *)
(* Actions                                                               *)
(* ---------------------------------------------------------------------- *)

(* Non-deterministically receive a subset of all sent messages *)
Receive(p) ==
    /\ p \in correct
    /\ \E new \in SUBSET sent :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
        /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(p) ==
    /\ p \in correct
    /\ pc[p] # "Bad"
    /\ <<pc[p], EchosCount(p)>> \in {<<"InitNoBroadcast", _>>, <<"EchoSent", _>>}
    /\ sent' = sent \cup {<<p, "ECHO">>}
    /\ pc' = [pc EXCEPT ![p] = IF pc[p] = "InitBroadcast" THEN "EchoSent"
                                   ELSE IF pc[p] = "InitNoBroadcast" THEN "EchoSent"
                                   ELSE pc[p]]
    /\ UNCHANGED <<recv, correct, faulty>>

Accept(p) ==
    /\ p \in correct
    /\ CanAccept(p)
    /\ pc' = [pc EXCEPT ![p] = "Accept"]
    /\ UNCHANGED <<sent, recv, correct, faulty>>

Next ==
    \/ \E p \in correct : Receive(p)
    \/ \E p \in correct : SendEcho(p)
    \/ \E p \in correct : Accept(p)
    \/ UNCHANGED <<correct, faulty, pc, sent, recv>>

(* ---------------------------------------------------------------------- *)
(* Specification                                                         *)
(* ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<pc, sent, recv, correct, faulty>>

(* ---------------------------------------------------------------------- *)
(* Type correctness invariant                                            *)
(* ---------------------------------------------------------------------- *)

TypeOK ==
    /\ correct \subseteq IDs
    /\ faulty = IDs \ correct
    /\ pc \in [IDs -> {"InitBroadcast", "InitNoBroadcast", "EchoSent", "Accept", "Bad"}]
    /\ sent \subseteq {<<i, "ECHO">> : i \in IDs}
    /\ recv \in [IDs -> SUBSET sent]

(* ---------------------------------------------------------------------- *)
(* Faulty correct work constraints                                         *)
(* ---------------------------------------------------------------------- *)

FCConstraints ==
    /\ Cardinality(correct) = N - F
    /\ Cardinality(faulty) = F
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

(* ---------------------------------------------------------------------- *)
(* Liveness properties (expressed as temporal formulas)                 *)
(* ---------------------------------------------------------------------- *)

CorrLtl == 
    \A p \in correct : (pc[p] = "InitBroadcast") => <> (pc[p] = "Accept")

RelayLtl == 
    \A p \in correct : (pc[p] = "Accept") => <> (\A q \in correct : pc[q] = "Accept")

UnforgLtl == 
    (\A p \in correct : pc[p] = "InitNoBroadcast") => [] (\A p \in correct : pc[p] # "Accept")

=============================================================================