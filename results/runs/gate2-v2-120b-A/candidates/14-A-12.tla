---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets, Boulanger

CONSTANTS N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
PROC == 1..N

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pc, ticket, nextTicket

\* ----------------------------------------------------------------------
\* Helper definitions for ticket handling
\* ----------------------------------------------------------------------
NextTicket(t) == 
  IF t = MaxNat THEN 0 ELSE t + 1

\* ----------------------------------------------------------------------
\* Initialization (inherits Boulanger's init, but restricts ticket range)
\* ----------------------------------------------------------------------
Init == 
  /\ pc = [i \in PROC |-> "idle"]
  /\ ticket = [i \in PROC |-> 0]
  /\ nextTicket = 0

\* ----------------------------------------------------------------------
\* Actions (inherit from Boulanger, with ticket range enforcement)
\* ----------------------------------------------------------------------
Acquire(i) == 
  /\ pc[i] = "idle"
  /\ ticket[i] = 0
  /\ ticket[i]' = nextTicket
  /\ nextTicket' = NextTicket(nextTicket)
  /\ pc[i]' = "waiting"
  /\ UNCHANGED << >>  \* other variables unchanged except as above

Enter(i) == 
  /\ pc[i] = "waiting"
  /\ \A j \in PROC :
        (j # i => 
           \/ ticket[j] = 0
           \/ (ticket[i] # ticket[j] /\ ticket[i] < ticket[j])
           \/ (ticket[i] = ticket[j] /\ i < j))
  /\ pc[i]' = "critical"
  /\ UNCHANGED << ticket, nextTicket >>

Release(i) == 
  /\ pc[i] = "critical"
  /\ pc[i]' = "idle"
  /\ ticket[i]' = 0
  /\ UNCHANGED nextTicket

\* ----------------------------------------------------------------------
\* Next-state relation (disjunction of all possible actions)
\* ----------------------------------------------------------------------
Next == 
  \E i \in PROC : Acquire(i) \/ Enter(i) \/ Release(i)

\* ----------------------------------------------------------------------
\* Full specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, ticket, nextTicket>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
MutualExclusion == 
  \A i, j \in PROC :
    (i # j) => ~ (pc[i] = "critical" /\ pc[j] = "critical")

TypeOK == 
  /\ pc \in [PROC -> {"idle", "waiting", "critical"}]
  /\ ticket \in [PROC -> Nat]
  /\ nextTicket \in Nat

Inv == 
  /\ MutualExclusion
  /\ TypeOK
  /\ nextTicket = 
       IF \E i \in PROC : ticket[i] = MaxNat
          THEN 0
          ELSE (nextTicket + 1) % (MaxNat + 1)

\* ----------------------------------------------------------------------
\* State constraint to keep tickets within finite range
\* ----------------------------------------------------------------------
StateConstraint == 
  /\ \A i \in PROC : ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* The specification exported to the .cfg file
\* ----------------------------------------------------------------------
SpecWithConstraint == Spec /\ StateConstraint

=============================================================================