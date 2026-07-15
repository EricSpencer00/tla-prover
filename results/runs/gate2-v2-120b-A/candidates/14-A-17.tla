---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,        \* number of processes
    MaxNat,   \* finite upper bound for natural numbers (exclusive)
    Nat       \* overridden set of natural numbers, defined in the .cfg

(*--------------------------------------------------------------------
  State variables (inherited from the Boulanger specification)
--------------------------------------------------------------------*)
VARIABLES
    nl,       \* array of natural numbers, one per process
    y,        \* ticket numbers, one per process
    pc        \* program counter / control state of each process

(*--------------------------------------------------------------------
  Constants and derived sets
--------------------------------------------------------------------*)
ProcSet == 1..N

(*--------------------------------------------------------------------
  Derived helpers
--------------------------------------------------------------------*)
TicketRange == 0..MaxNat

IsValidTicket(t) == t \in TicketRange

(*--------------------------------------------------------------------
  Initial state (inherits Boulanger's init, with Nat restricted)
--------------------------------------------------------------------*)
Init ==
    /\ nl = [p \in ProcSet |-> 0]
    /\ y  = [p \in ProcSet |-> 0]
    /\ pc = [p \in ProcSet |-> "init"]
    /\ \A p \in ProcSet: IsValidTicket(y[p])

(*--------------------------------------------------------------------
  Actions (inherited from Boulanger, expressed succinctly)
--------------------------------------------------------------------*)
NonCritical(p) ==
    /\ pc[p] = "init"
    /\ pc' = [pc EXCEPT ![p] = "want"]
    /\ UNCHANGED <<nl, y>>

BeginTry(p) ==
    /\ pc[p] = "want"
    /\ nl' = [nl EXCEPT ![p] = Max({nl[q] : q \in ProcSet}) + 1]
    /\ pc' = [pc EXCEPT ![p] = "try"]
    /\ UNCHANGED y
    /\ nl[p] =< MaxNat        \* keep within finite range

SetTicket(p) ==
    /\ pc[p] = "try"
    /\ y' = [y EXCEPT ![p] = nl[p]]
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ IsValidTicket(y'[p])
    /\ UNCHANGED nl

ExitCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<nl, y>>

Reset(p) ==
    /\ pc[p] = "exit"
    /\ nl' = [nl EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "init"]
    /\ UNCHANGED y

Next ==
    \E p \in ProcSet: \/ NonCritical(p)
                       \/ BeginTry(p)
                       \/ SetTicket(p)
                       \/ ExitCS(p)
                       \/ Reset(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<nl, y, pc>>

(*--------------------------------------------------------------------
  Safety invariants (inherited from Boulanger)
--------------------------------------------------------------------*)
MutualExclusion ==
    \A p, q \in ProcSet :
        (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

TypeOK ==
    /\ nl \in [ProcSet -> TicketRange]
    /\ y  \in [ProcSet -> TicketRange]
    /\ pc \in [ProcSet -> {"init", "want", "try", "cs", "exit"}]

Inv == MutualExclusion /\ TypeOK

=============================================================================