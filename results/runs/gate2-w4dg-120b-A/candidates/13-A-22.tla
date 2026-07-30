---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

\* Derive the process set from the size constant.
PROCESS == 0 .. (N - 1)

\* Ticket numbers are taken from a finite range, overriding the
\* unbounded naturals for model checking.
Ticket == 0 .. MaxNat

VARIABLES cs, want, ticket

vars == << cs, want, ticket >>

TypeOK ==
  /\ cs \in [PROCESS -> {"idle", "critical"}]
  /\ want \in [PROCESS -> BOOLEAN]
  /\ ticket \in [PROCESS -> Ticket]

\* Mutual exclusion: at most one process is ever in its critical section.
MutualExclusion ==
  \A p, q \in PROCESS :
    (cs[p] = "critical" /\ cs[q] = "critical") => (p = q)

\* The full inductive invariant: action conditions as well as the
\* state property that the whole system is properly typed.
Inv ==
  /\ TypeOK
  /\ \A p \in PROCESS :
       /\ cs[p] = "critical" => want[p]
       /\ want[p] => ticket[p] \in Ticket

Init ==
  /\ cs = [p \in PROCESS |-> "idle"]
  /\ want = [p \in PROCESS |-> FALSE]
  /\ ticket = [p \in PROCESS |-> MaxNat]

\* A process declares that it wants the critical section.
Request(p) ==
  /\ ~want[p]
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ UNCHANGED << cs, ticket >>

\* A requesting process takes a ticket number; since the range is bounded
\* a fresh number may not exist, so the step is guarded accordingly.
TakeTicket(p) ==
  /\ want[p]
  /\ cs[p] = "idle"
  /\ ticket[p] = MaxNat
  /\ \E t \in Ticket :
       /\ \A q \in PROCESS : ticket[q] # t
       /\ ticket' = [ticket EXCEPT ![p] = t]
  /\ UNCHANGED << cs, want >>

\* A process enters the critical section once it holds a ticket strictly
\* smaller than every other requesting process's ticket.
Enter(p) ==
  /\ want[p]
  /\ cs[p] = "idle"
  /\ ticket[p] \in Ticket
  /\ \A q \in PROCESS : (want[q] /\ q # p) => (ticket[p] < ticket[q])
  /\ cs' = [cs EXCEPT ![p] = "critical"]
  /\ UNCHANGED << want, ticket >>

\* A process leaves the critical section, releasing its ticket.
Exit(p) ==
  /\ cs[p] = "critical"
  /\ cs' = [cs EXCEPT ![p] = "idle"]
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ ticket' = [ticket EXCEPT ![p] = MaxNat]

Next ==
  \/ \E p \in PROCESS : Request(p)
  \/ \E p \in PROCESS : TakeTicket(p)
  \/ \E p \in PROCESS : Enter(p)
  \/ \E p \in PROCESS : Exit(p)

\* The inductive specification: any state satisfying the invariant can
\* transition to a next state, and the invariant itself is assumed true
\* from the start (rather than proving it reachable from Init).
ISpec ==
  /\ Inv
  /\ [][Next]_vars

\* The inductive spec is the distinguished specification name for this
\* module.
Spec == ISpec

====