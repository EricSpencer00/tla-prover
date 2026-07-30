---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* The finite override of natural numbers is a bounded range; the state
\* constraint below keeps ticket numbers strictly below MaxNat so the
\* override never gets exhausted during the run.
VARIABLES cs, tickets, maxTicket

vars == <<cs, tickets, maxTicket>>

TypeOK ==
  /\ cs \in [1..N -> {"idle", "wait", "cs"}]
  /\ tickets \in [1..N -> 0..MaxNat]
  /\ maxTicket \in 0..MaxNat

Init ==
  /\ cs = [i \in 1..N |-> "idle"]
  /\ tickets = [i \in 1..N |-> 0]
  /\ maxTicket = 0

\* Acquire: a process advances its ticket and enters the wait set.
Acquire(i) ==
  /\ cs[i] = "idle"
  /\ tickets[i] = maxTicket
  /\ maxTicket < MaxNat
  /\ tickets' = [tickets EXCEPT ![i] = tickets[i] + 1]
  /\ maxTicket' = tickets[i] + 1
  /\ cs' = [cs EXCEPT ![i] = "wait"]

\* Enter: the process with the smallest ticket among the waiters enters CS.
Enter(i) ==
  /\ cs[i] = "wait"
  /\ \A j \in 1..N : cs[j] # "cs" \/ tickets[i] <= tickets[j]
  /\ cs' = [cs EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<tickets, maxTicket>>

\* Exit: the process leaves the critical section.
Exit(i) ==
  /\ cs[i] = "cs"
  /\ cs' = [cs EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<tickets, maxTicket>>

Next ==
  \/ \E i \in 1..N : Acquire(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (cs[i] = "cs" /\ cs[j] = "cs") => i = j

Inv == TypeOK /\ MutualExclusion

StateConstraint ==
  \A i \in 1..N : tickets[i] <= MaxNat - 1

====