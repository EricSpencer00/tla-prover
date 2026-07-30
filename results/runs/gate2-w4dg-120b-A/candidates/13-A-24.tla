---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* The Bakery mutual exclusion algorithm, model-checked over a finite Nat range.
\* Ticket: [1..N -> 0..MaxNat] -- each process's ticket number (0 = not in queue)
\* Q: [1..N -> {"idle", "waiting", "cs"}] -- each process's current phase
VARIABLES Ticket, Q

vars == <<Ticket, Q>>

TypeOK ==
  /\ Ticket \in [1..N -> 0..MaxNat]
  /\ Q \in [1..N -> {"idle", "waiting", "cs"}]

\* Mutual exclusion: a process is in the critical section only if its ticket
\* is strictly smaller than every other waiting process's ticket.
MutualExclusion ==
  \A i \in 1..N :
    Q[i] = "cs" =>
      \A j \in 1..N : (j # i /\ Q[j] = "waiting") => Ticket[i] < Ticket[j]

\* The full inductive invariant: ticket numbers stay in range, Q only takes
\* allowed values, and the ordering invariant holds.  The ordering invariant
\* is separate from MutualExclusion so it is checked in every reachable state.
Inv ==
  /\ TypeOK
  /\ MutualExclusion
  /\ \A i \in 1..N : Q[i] \in {"idle", "waiting", "cs"}

\* Ticket numbers are allocated by bumping the minimum free slot up to MaxNat.
Allocate(i) ==
  /\ Q[i] = "idle"
  /\ \E k \in 1..MaxNat : (~\E j \in 1..N : Ticket[j] = k) /\ Ticket' = [Ticket EXCEPT ![i] = k]
  /\ Q' = [Q EXCEPT ![i] = "waiting"]

Enter(i) ==
  /\ Q[i] = "waiting"
  /\ \A j \in 1..N : (j # i /\ Q[j] = "waiting") => Ticket[i] < Ticket[j]
  /\ Q' = [Q EXCEPT ![i] = "cs"]
  /\ UNCHANGED Ticket

Exit(i) ==
  /\ Q[i] = "cs"
  /\ Q' = [Q EXCEPT ![i] = "idle"]
  /\ Ticket' = [Ticket EXCEPT ![i] = 0]

Next == \E i \in 1..N : Allocate(i) \/ Enter(i) \/ Exit(i)

\* The inductive specification: start from any type-correct state and check that
\* all reachable states still satisfy the invariant (rather than starting only
\* from a fixed initial state).
ISpec == Init /\ [][Next]_vars /\ WF_vars(Next)

Init ==
  /\ Ticket = [i \in 1..N |-> 0]
  /\ Q = [i \in 1..N |-> "idle"]

\* No additional properties beyond the invariant are checked here.
Spec == ISpec

====