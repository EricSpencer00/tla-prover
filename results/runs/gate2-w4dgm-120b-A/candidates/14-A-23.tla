---- MODULE MCBoulanger ----
EXTENDS Naturals

\* A finite override of the natural numbers for model checking: Nat is kept as
\* a defined operator (replacing the standard Naturals.Nat) but runs over only
\* the range 0..MaxNat instead of the full infinite set.
CONSTANTS N, MaxNat

\* Replaces Naturals.Nat with a finite version so the model stays finite.
Nat == 0..MaxNat

VARIABLES state, ticket, dispensed, total

vars == <<state, ticket, dispensed, total>>

TypeOK ==
  /\ state \in [1..N -> {"idle", "trying", "critical", "holding"}]
  /\ ticket \in [1..N -> Nat]
  /\ dispensed \in Nat
  /\ total \in Nat

Init ==
  /\ state = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ dispensed = 0
  /\ total = 0

\* A process moves to critical section only when no one else holds the ticket.
Enter(i) ==
  /\ state[i] = "trying"
  /\ \A k \in 1..N : state[k] # "critical"
  /\ state' = [state EXCEPT ![i] = "critical"]
  /\ UNCHANGED <<ticket, dispensed, total>>

\* Exiting the critical section bumps the ticket and the shared dough total together.
Exit(i) ==
  /\ state[i] = "critical"
  /\ ticket[i] < MaxNat
  /\ state' = [state EXCEPT ![i] = "holding"]
  /\ ticket' = [ticket EXCEPT ![i] = ticket[i] + 1]
  /\ total' = total + 1
  /\ UNCHANGED dispensed

\* An idle process starts contending for the critical section.
StartAttempt(i) ==
  /\ state[i] = "idle"
  /\ state' = [state EXCEPT ![i] = "trying"]
  /\ UNCHANGED <<ticket, dispensed, total>>

\* A holding process returns to idle once its ticket budget is spent.
Finish(i) ==
  /\ state[i] = "holding"
  /\ state' = [state EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<ticket, dispensed, total>>

\* The irreversible step: a process does one final action and never repeats it.
Dispense(i) ==
  /\ state[i] = "idle"
  /\ dispensed = 0
  /\ dispensed' = dispensed + 1
  /\ total' = total + 1
  /\ UNCHANGED <<state, ticket>>

Next ==
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)
  \/ \E i \in 1..N : StartAttempt(i)
  \/ \E i \in 1..N : Finish(i)
  \/ \E i \in 1..N : Dispense(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (state[i] = "critical" /\ state[j] = "critical") => i = j

Inv ==
  \A i, j \in 1..N :
    (state[i] = "holding" /\ state[j] = "holding") => (i = j \/ ticket[i] # ticket[j])

TicketBudgetRespected == \A i \in 1..N : ticket[i] <= MaxNat
FiniteRange == total <= MaxNat

====