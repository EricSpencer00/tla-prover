---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, MaxNat

Nat == 0 .. MaxNat

VARIABLES choose, ticket, cs

(* ----------------------------------------------------------------------
   Initialization
   ---------------------------------------------------------------------- *)
Init ==
    /\ choose = [i \in 0..N-1 |-> 0]
    /\ ticket = [i \in 0..N-1 |-> 0]
    /\ cs    = [i \in 0..N-1 |-> FALSE]

(* ----------------------------------------------------------------------
   Helper predicates
   ---------------------------------------------------------------------- *)
InCS(i) == cs[i]

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

Choose(i) ==
    /\ choose' = [choose EXCEPT ![i] = 1]
    /\ UNCHANGED << ticket, cs >>

Ticket(i) ==
    /\ ticket' = [ticket EXCEPT ![i] = CHOOSE n \in Nat : n \notin (VALUES ticket)]
    /\ UNCHANGED << choose, cs >>

EnterCS(i) ==
    /\ cs' = [cs EXCEPT ![i] = TRUE]
    /\ UNCHANGED << choose, ticket >>

ExitCS(i) ==
    /\ cs' = [cs EXCEPT ![i] = FALSE]
    /\ UNCHANGED << choose, ticket >>

Next ==
    \E i \in 0..N-1 :
        \/ Choose(i)
        \/ Ticket(i)
        \/ EnterCS(i)
        \/ ExitCS(i)

(* ----------------------------------------------------------------------
   Specification (inductive)
   ---------------------------------------------------------------------- *)
ISpec == Init /\ [][Next]_<<choose, ticket, cs>>

(* ----------------------------------------------------------------------
   Type Correctness
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ \A i \in 0..N-1 : choose[i] \in Bool
    /\ \A i \in 0..N-1 : ticket[i] \in Nat
    /\ \A i \in 0..N-1 : cs[i] \in Bool

(* ----------------------------------------------------------------------
   Mutual Exclusion
   ---------------------------------------------------------------------- *)
MutualExclusion ==
    \A i, j \in 0..N-1 : (i # j) => ~(cs[i] /\ cs[j])

(* ----------------------------------------------------------------------
   Full Inductive Invariant (as defined by the Bakery algorithm)
   ---------------------------------------------------------------------- *)
Inv ==
    /\ \A i \in 0..N-1 : ticket[i] \in Nat
    /\ \A i \in 0..N-1 :
        cs[i] => \A j \in 0..N-1 :
            (j # i) => ticket[j] = 0 \/ ticket[j] < ticket[i] \/ (ticket[j] = ticket[i] /\ j < i)

====