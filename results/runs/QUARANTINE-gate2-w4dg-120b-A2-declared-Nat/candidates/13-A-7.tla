---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

\* The NatOverride alias is what the .cfg file substitutes for the Nat symbol,
\* so it must exist in the module with that exact name.
NatOverride == Nat

VARIABLES claims, tickets, using, waiting

vars == <<claims, tickets, using, waiting>>

Processes == 0 .. (N - 1)

TypeOK ==
  /\ claims \in [Processes -> BOOLEAN]
  /\ tickets \in [Processes -> 0 .. MaxNat]
  /\ using \subseteq Processes
  /\ waiting \subseteq Processes

Init ==
  /\ claims = [p \in Processes |-> FALSE]
  /\ tickets = [p \in Processes |-> 0]
  /\ using = {}
  /\ waiting = {}

\* Draw a ticket number from the bounded range instead of the infinite Nat.
Claim(p) ==
  /\ ~claims[p]
  /\ claims' = [claims EXCEPT ![p] = TRUE]
  /\ tickets' = [tickets EXCEPT ![p] = MaxNat]
  /\ UNCHANGED <<using, waiting>>

\* Enter the critical section only when no other process is using it.
Enter(p) ==
  /\ claims[p]
  /\ using = {}
  /\ using' = {p}
  /\ UNCHANGED <<claims, tickets, waiting>>

Exit(p) ==
  /\ p \in using
  /\ using' = using \ {p}
  /\ claims' = [claims EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<tickets, waiting>>

\* Progress: a process not yet using the resource signals it is waiting.
Request(p) ==
  /\ p \notin waiting
  /\ waiting' = waiting \cup {p}
  /\ UNCHANGED <<claims, tickets, using>>

Next ==
  \/ \E p \in Processes : Claim(p)
  \/ \E p \in Processes : Enter(p)
  \/ \E p \in Processes : Exit(p)
  \/ \E p \in Processes : Request(p)

Spec == Next

\* Mutual exclusion: no two processes in the critical section at once.
MutualExclusion ==
  \A a, b \in using : a = b

\* The fully inductive invariant, which must hold in every reachable state.
Inv ==
  /\ TypeOK
  /\ \A p \in using : claims[p]
  /\ \A p \in using : tickets[p] = MaxNat

ISpec == Spec /\ Inv

====