---- MODULE W4Od11m6p3t0 ----
EXTENDS Naturals

CONSTANTS Slots, Jobs

VARIABLES
  grants,   \* set of <<slot, job, leaseEnd>> active print-slot leases
  clock,    \* current logical clock
  printed,  \* set of <<slot, job>> jobs that finished printing
  crashed   \* set of jobs whose client crashed silently

vars == <<grants, clock, printed, crashed>>

MaxTime == 3
LeaseK  == 2
SlotOf(g) == g[1]
JobOf(g)  == g[2]
EndOf(g)  == g[3]
SlotLeased(s) == \E g \in grants : SlotOf(g) = s

TypeOK ==
  /\ grants \subseteq (Slots \X Jobs \X (0..MaxTime))
  /\ clock \in 0..MaxTime
  /\ printed \subseteq (Slots \X Jobs)
  /\ crashed \subseteq Jobs

Init ==
  /\ grants = {}
  /\ clock = 0
  /\ printed = {}
  /\ crashed = {}

\* A live job leases a currently-unleased print slot until LeaseK ticks from now
Lease(s, j) ==
  /\ j \notin crashed
  /\ ~SlotLeased(s)
  /\ clock + LeaseK <= MaxTime
  /\ grants' = grants \cup {<<s, j, clock + LeaseK>>}
  /\ UNCHANGED <<clock, printed, crashed>>

\* The lease-holder prints on its slot while the lease is still valid
DoPrint(s, j, e) ==
  /\ <<s, j, e>> \in grants
  /\ e > clock
  /\ printed' = printed \cup {<<s, j>>}
  /\ UNCHANGED <<grants, clock, crashed>>

\* An expired lease is reclaimed, freeing the slot
Expire(s, j, e) ==
  /\ <<s, j, e>> \in grants
  /\ e <= clock
  /\ grants' = grants \ {<<s, j, e>>}
  /\ UNCHANGED <<clock, printed, crashed>>

\* Time advances one tick
Tick ==
  /\ clock < MaxTime
  /\ clock' = clock + 1
  /\ UNCHANGED <<grants, printed, crashed>>

\* A job's client crashes silently, dropping all of that job's leases
Crash(j) ==
  /\ j \notin crashed
  /\ crashed' = crashed \cup {j}
  /\ grants' = { g \in grants : JobOf(g) # j }
  /\ UNCHANGED <<clock, printed>>

\* A job's client is restarted and rejoins
Recover(j) ==
  /\ j \in crashed
  /\ crashed' = crashed \ {j}
  /\ UNCHANGED <<grants, clock, printed>>

Next ==
  \/ \E s \in Slots, j \in Jobs : Lease(s, j)
  \/ \E s \in Slots, j \in Jobs, e \in 0..MaxTime : DoPrint(s, j, e)
  \/ \E s \in Slots, j \in Jobs, e \in 0..MaxTime : Expire(s, j, e)
  \/ Tick
  \/ \E j \in Jobs : Crash(j)
  \/ \E j \in Jobs : Recover(j)

Spec == Init /\ [][Next]_vars

\* No print slot is ever leased to two different jobs at the same time
NoDoubleAlloc ==
  \A x, y \in grants : (SlotOf(x) = SlotOf(y)) => (JobOf(x) = JobOf(y))
====