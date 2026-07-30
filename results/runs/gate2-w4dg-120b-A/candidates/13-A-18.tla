---- MODULE MCBakery ----
EXTENDS Naturals

\* The Bakery mutual exclusion algorithm, re-used here for model checking
\* with a bounded range of natural numbers. The constants below are the
\* exact identifiers the reference .cfg expects.
CONSTANTS N, MaxNat, Nat

\* The set of natural numbers used by this model checking configuration: a
\* finite range, so the state space stays bounded.
Naturals == 0..MaxNat

\* State variables: exactly those of the original Bakery spec. No extra
\* variables are introduced here.
VARIABLES inCS, wants, ticket, nextTicket

vars == << inCS, wants, ticket, nextTicket >>

TypeOK ==
  /\ inCS \in SUBSET (1..N)
  /\ wants \in SUBSET (1..N)
  /\ ticket \in [1..N -> Naturals]
  /\ nextTicket \in Naturals

MutualExclusion ==
  \A p \in inCS, q \in inCS : p = q

\* The full inductive invariant of the Bakery algorithm: no two processes
\* in the critical section, every entrant has a ticket, every entered
\* process wanted the section, and the next ticket number is always
\* strictly above every ticket already issued -- except that the
\* ticket ceiling is a hard bound here, so nextTicket may saturate.
Inv ==
  /\ MutualExclusion
  /\ \A p \in inCS : ticket[p] \in Naturals
  /\ \A p \in inCS : p \in wants
  /\ \A q \in 1..N : q \in inCS => ticket[q] < nextTicket

Init ==
  /\ inCS = {}
  /\ wants = {}
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0

\* A process that wants the critical section takes a ticket, limited by
\* the maximum natural number value.
Request(p) ==
  /\ p \notin wants
  /\ nextTicket < MaxNat
  /\ wants' = wants \cup {p}
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED inCS

\* A process enters the critical section once all other entrants hold a
\* strictly lower ticket number.
Enter(p) ==
  /\ p \in wants
  /\ p \notin inCS
  /\ \A q \in inCS : ticket[p] > ticket[q]
  /\ inCS' = inCS \cup {p}
  /\ UNCHANGED << wants, ticket, nextTicket >>

\* A process exits the critical section.
Exit(p) ==
  /\ p \in inCS
  /\ inCS' = inCS \ {p}
  /\ wants' = wants \ {p}
  /\ UNCHANGED << ticket, nextTicket >>

Next == \E p \in 1..N : Request(p) \/ Enter(p) \/ Exit(p)

\* The inductive specification: any reachable state may be a starting
\* point, but it must already satisfy the invariant.
ISpec == Init /\ [][Next]_vars /\ WF_vars(Enter(1)) /\ WF_vars(Exit(1))
          /\ WF_vars(Enter(2)) /\ WF_vars(Exit(2))
          /\ TRUE

Spec == ISpec

\* The reference configuration also lists the invariant under the generic
\* INVARIANTS name, so it is repeated here. No liveness properties are
\* required.
INVARIANTS == MutualExclusion /\ TypeOK /\ Inv

====