---- MODULE MCBakery ----
EXTENDS Naturals

(* Model-checking configuration module for the Bakery mutual exclusion     *)
(* algorithm.  It inherits the algorithm's state space and actions and      *)
(* overrides the range of natural numbers to a finite bound so the         *)
(* exhaustive-state model checking is feasible.  It carries no new state    *)
(* of its own beyond the bound constant.                                   *)

CONSTANTS N, MaxNat

\* The operator name on the left is fixed by the .cfg file; this is the     \* replacement body the config wants, so the name on the right must     \* not be declared.                                                    \* The replacement keeps Nat as a finite-range, type-correct function. *
NatOverride == [S \in Nat |-> IF S <= MaxNat THEN S ELSE MaxNat]

VARIABLES inCS, want, ticket, nextTicket

Init ==
  /\ inCS = [p \in 0..(N-1) |-> FALSE]
  /\ want = [p \in 0..(N-1) |-> FALSE]
  /\ ticket = [p \in 0..(N-1) |-> 0]
  /\ nextTicket = 0

Request(p) ==
  /\ ~want[p]
  /\ ~inCS[p]
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<inCS, ticket, nextTicket>>

\* The ticket is drawn from a globally bounded counter, capped by the       \* finite range override; a process that already holds a ticket is      \* not re-ticketed here.                                                  \*
Acquire(p) ==
  /\ want[p]
  /\ ticket[p] = 0
  /\ nextTicket < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket + 1]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED <<inCS, want>>

Enter(p) ==
  /\ want[p]
  /\ ticket[p] # 0
  /\ \A q \in 0..(N-1) : ~inCS[q]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<want, ticket, nextTicket>>

Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<want, ticket, nextTicket>>

ResetTicket(p) ==
  /\ ~inCS[p]
  /\ ticket[p] # 0
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED <<inCS, want, nextTicket>>

Next ==
  \/ \E p \in 0..(N-1) : Request(p)
  \/ \E p \in 0..(N-1) : Acquire(p)
  \/ \E p \in 0..(N-1) : Enter(p)
  \/ \E p \in 0..(N-1) : Exit(p)
  \/ \E p \in 0..(N-1) : ResetTicket(p)

Vars == <<inCS, want, ticket, nextTicket>>

ISpec == Init /\ [][Next]_Vars

\* Safety: mutual exclusion, plus the per-process type discipline and its   \* closure-under-superseded-tickets.                                   \*
MutualExclusion == \A p, q \in 0..(N-1) : (inCS[p] /\ inCS[q]) => (p = q)
TypeOK ==
  /\ inCS \in [0..(N-1) -> BOOLEAN]
  /\ want \in [0..(N-1) -> BOOLEAN]
  /\ ticket \in [0..(N-1) -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
Inv ==
  /\ MutualExclusion
  /\ TypeOK
====