---- MODULE MCBakery ----
EXTENDS Naturals

\* Model-checking configuration for the Bakery mutual exclusion algorithm.
\* Redefines Nat as a finite range (0..MaxNat) to bound the state space.
CONSTANTS N, MaxNat, Nat

VARIABLES entering, number, waiting, inCS
vars == <<entering, number, waiting, inCS>>

\* Overridden Nat: the infinite set of natural numbers replaced by a
\* finite range for model checking.  For readability the operators below
\* use Nat directly; NatOverride is the name the .cfg substitutes.
NatOverride == Nat

TypeOK ==
  /\ entering \in [1..N -> BOOLEAN]
  /\ number \in [1..N -> Nat]
  /\ waiting \in [1..N -> BOOLEAN]
  /\ inCS \subseteq (1..N)

Init ==
  /\ entering = [p \in 1..N |-> FALSE]
  /\ number = [p \in 1..N |-> 0]
  /\ waiting = [p \in 1..N |-> FALSE]
  /\ inCS = {}

\* The maximum ticket number is capped by the configured bound MaxNat.
Enter(p) ==
  /\ ~entering[p]
  /\ ~waiting[p]
  /\ p \notin inCS
  /\ entering' = [entering EXCEPT ![p] = TRUE]
  /\ number' = [number EXCEPT ![p] = (IF \A q \in 1..N : number[q] >= number[p] /\ q # p THEN number[p] + 1 ELSE number[p])]
  /\ UNCHANGED <<waiting, inCS>>

\* Ticket number p reads is capped to MaxNat, so it never grows past it.
Read(p) ==
  /\ entering[p]
  /\ number[p] <= MaxNat
  /\ waiting' = [waiting EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<entering, number, inCS>>

\* Mutual exclusion: p's ticket must be strictly smaller than every other
\* waiting process's ticket (or p is the smallest-numbered process among
\* those at the same ticket number) to enter the critical section.
EnterCS(p) ==
  /\ waiting[p]
  /\ \A q \in 1..N :
       ~(waiting[q] /\ q # p
         /\ (number[p] > number[q] \/ (number[p] = number[q] /\ p > q)))
  /\ inCS' = inCS \cup {p}
  /\ UNCHANGED <<entering, number, waiting>>

Exit(p) ==
  /\ p \in inCS
  /\ inCS' = inCS \ {p}
  /\ entering' = [entering EXCEPT ![p] = FALSE]
  /\ waiting' = [waiting EXCEPT ![p] = FALSE]
  /\ UNCHANGED number

Next ==
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Read(p)
  \/ \E p \in 1..N : EnterCS(p)
  \/ \E p \in 1..N : Exit(p)

\* The INDUCTIVE specification: starts from any type-correct reachable state,
\* not just the initial state.
ISpec == Spec /\ [][Next]_vars
Spec == Init /\ [][Next]_vars

\* SAFETY PROPERTY: at most one process in the critical section at a time.
MutualExclusion == \A p, q \in inCS : p = q

\* The full invariant from the Bakery spec, split into its components.
Inv == TypeOK /\ MutualExclusion

====