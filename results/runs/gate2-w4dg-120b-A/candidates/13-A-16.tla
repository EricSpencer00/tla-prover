---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* The set of processes is a fixed range 1..N
PROCESSES == 1..N

VARIABLES ticket, using, waiting

vars == <<ticket, using, waiting>>

TypeOK ==
  /\ ticket \in [PROCESSES -> 0..MaxNat]
  /\ using \in [PROCESSES -> BOOLEAN]
  /\ waiting \in SUBSET PROCESSES

\* No two distinct processes are ever simultaneously in the critical section.
MutualExclusion ==
  \A i \in PROCESSES : using[i] => \A j \in PROCESSES \ {i} : ~using[j]

\* The bakery invariant: type-correctness plus mutual exclusion.
Inv == TypeOK /\ MutualExclusion

Init ==
  /\ ticket = [i \in PROCESSES |-> 0]
  /\ using = [i \in PROCESSES |-> FALSE]
  /\ waiting = {}

\* A process takes a ticket and joins the waiting pool.
Take(i) ==
  /\ ~using[i]
  /\ i \notin waiting
  /\ ticket' = [ticket EXCEPT ![i] = MaxNat + 1]
  /\ waiting' = waiting \cup {i}
  /\ UNCHANGED using

\* The lowest ticket-holder may enter the critical section; unused tickets are reset.
Enter(i) ==
  /\ i \in waiting
  /\ \A j \in waiting : ticket[j] >= ticket[i]
  /\ using[i] = FALSE
  /\ ticket[i] <= MaxNat
  /\ using' = [using EXCEPT ![i] = TRUE]
  /\ waiting' = waiting \ {i}
  /\ UNCHANGED ticket

\* A process leaves the critical section and frees its ticket.
Exit(i) ==
  /\ using[i]
  /\ using' = [using EXCEPT ![i] = FALSE]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED waiting

Next ==
  \/ \E i \in PROCESSES : Take(i)
  \/ \E i \in PROCESSES : Enter(i)
  \/ \E i \in PROCESSES : Exit(i)

ISpec == Init /\ [][Next]_vars

====