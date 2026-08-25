---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

(* ----------------------------------------------------------------------
   Process set
   ---------------------------------------------------------------------- *)
Proc == 1..N

VARIABLES Correct, Faulty, pc, recv, Sent

vars == <<Correct, Faulty, pc, recv, Sent>>

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
EchoCount(p) == Cardinality(recv[p])

IsCorrect(p) == p \in Correct
IsFaulty(p) == p \in Faulty

SentEcho(p) == p \in Sent

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc \in [Proc -> {"NoInit", "InitRec", "EchoSent", "Accepted"}]
    /\ recv \in [Proc -> SUBSET Proc]
    /\ Sent = {}

(* ----------------------------------------------------------------------
   Receive action: a correct process may learn any new set of ECHO
   messages (including those possibly forged by Byzantine processes).
   ---------------------------------------------------------------------- *)
Receive(p) ==
    /\ p \in Correct
    /\ \E newSet \in SUBSET Proc :
          /\ recv[p] \subseteq newSet
          /\ recv' = [recv EXCEPT ![p] = newSet]
          /\ UNCHANGED <<Correct, Faulty, pc, Sent>>

(* ----------------------------------------------------------------------
   SendEcho (and possibly Accept) action for a correct process.
   ---------------------------------------------------------------------- *)
SendEcho(p) ==
    /\ p \in Correct
    /\ LET cnt == EchoCount(p) IN
       /\ \/ pc[p] = "InitRec"
          \/ /\ pc[p] = "NoInit"
             /\ ~SentEcho(p)
             /\ cnt >= N - 2 * T
             /\ cnt < N - T
          \/ /\ pc[p] = "NoInit"
             /\ ~SentEcho(p)
             /\ cnt >= N - T
          \/ /\ pc[p] = "EchoSent"
             /\ cnt >= N - T
    /\ Sent' = Sent \cup {p}
    /\ pc' = [pc EXCEPT ![p] =
                IF pc[p] = "InitRec" \/
                   (pc[p] = "NoInit" /\ ~SentEcho(p) /\ cnt >= N - T) \/
                   (pc[p] = "EchoSent" /\ cnt >= N - T)
                THEN "Accepted"
                ELSE "EchoSent"]
    /\ UNCHANGED <<Correct, Faulty, recv>>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ \E p \in Correct : Receive(p)
    \/ \E p \in Correct : SendEcho(p)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Faulty = Proc \ Correct
    /\ Cardinality(Correct) = N - F
    /\ pc \in [Proc -> {"NoInit", "InitRec", "EchoSent", "Accepted"}]
    /\ recv \in [Proc -> SUBSET Proc]
    /\ Sent \subseteq Correct

(* ----------------------------------------------------------------------
   Fault‑tolerance constraints
   ---------------------------------------------------------------------- *)
FCConstraints == N > 3 * T /\ T >= F /\ F >= 0

(* ----------------------------------------------------------------------
   LTL properties
   ---------------------------------------------------------------------- *)
CorrLtl == ( \A p \in Correct : pc[p] = "InitRec" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

RelayLtl == ( \E p \in Correct : pc[p] = "Accepted" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

UnforgLtl == ( \A p \in Correct : pc[p] = "NoInit" ) => [] ( \A p \in Correct : pc[p] # "Accepted" )

=============================================================================