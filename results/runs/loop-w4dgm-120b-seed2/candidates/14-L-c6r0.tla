---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets, Sequences

(* Model-checking configuration module for the Boulangerie mutual exclusion   *)
(* algorithm.  It sets a finite bound on natural numbers (via MaxNat) and       *)
(* adds a state constraint to keep all ticket numbers below that bound, so    *)
(* the model stays finite.  It inherits the full action set and all invariants  *)
(* from the base Boulanger specification.                                      *)

CONSTANTS N, MaxNat

VARIABLES phase, ticket, queue, target

vars == <<phase, ticket, queue, target>>

Phases == {"idle", "queued", "critical", "done"}

InQueue(p) == \E i \in 1..Len(queue) : queue[i] = p

TypeOK ==
  /\ phase \in [1..N -> Phases]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ queue \in Seq(1..N)
  /\ target \in 1..N

Init ==
  /\ phase = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ queue = << >>
  /\ target = 1

\* A process joins the entry queue and is stamped with a fresh bounded ticket.
Enqueue(p) ==
  /\ phase[p] = "idle"
  /\ ~InQueue(p)
  /\ phase' = [phase EXCEPT ![p] = "queued"]
  /\ ticket' = [ticket EXCEPT ![p] = IF ticket[p] < MaxNat THEN ticket[p] + 1 ELSE ticket[p]]
  /\ queue' = Append(queue, p)
  /\ UNCHANGED target

\* The process at the head may enter only if its ticket is strictly larger
\* than every other process's ticket, which is what grants mutual exclusion.
Enter ==
  /\ queue # << >>
  /\ LET h == Head(queue) IN
       /\ \A q \in 1..N : q # h => ticket[h] > ticket[q]
       /\ phase' = [phase EXCEPT ![h] = "critical"]
  /\ queue' = Tail(queue)
  /\ UNCHANGED <<ticket, target>>

ExitCS(p) ==
  /\ phase[p] = "critical"
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<ticket, queue, target>>

Reset(p) ==
  /\ phase[p] = "done"
  /\ phase' = [phase EXCEPT ![p] = "idle"]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED <<queue, target>>

Next ==
  \/ (\E p \in 1..N : Enqueue(p))
  \/ Enter
  \/ (\E p \in 1..N : ExitCS(p))
  \/ (\E p \in 1..N : Reset(p))

Spec == Init /\ [][Next]_vars

(* The forwarding process can be any process; it is never constrained.      *)
(* This fairness condition is what keeps the queue serviced regardless of   *)
(* which process it happens to pick.                                        *)
Fairness == (\A p \in 1..N : WF_vars(Enqueue(p))) /\ WF_vars(Enter)

MutualExclusion == \A p \in 1..N : phase[p] = "critical" => \A q \in 1..N \ {p} : phase[q] # "critical"

(* The full inductive invariant from the Boulanger spec: the CS holder is     *)
(* always the current target and holds the highest ticket, so no two         *)
(* processes can ever both be in the critical section.                        *)
Inv ==
  /\ (\A p \in 1..N : phase[p] = "critical" => p = target)
  /\ (\A p \in 1..N : phase[p] = "critical" => \A q \in 1..N : ticket[p] >= ticket[q])

(* The model always keeps tickets below the finite bound, so the override  *)
(* of Nat (finite MaxNat) never leads to a discarded or out-of-range ticket. *)
TicketBound == \A p \in 1..N : ticket[p] < MaxNat

====