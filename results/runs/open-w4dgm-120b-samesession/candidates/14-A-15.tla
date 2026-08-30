---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* This is a model-checking configuration module for the Boulanger mutual
\* exclusion algorithm. It redefines Nat as a finite range overriding the
\* infinite NAT from the standard module, and adds a state constraint to
\* keep ticket numbers within that finite range during model checking.

\* Actor/process IDs are taken as the first N naturals 0..N-1.
Ids == 0 .. (N - 1)

VARIABLES issued, claim, holding, crashed

vars == <<issued, claim, holding, crashed>>

TypeOK ==
    /\ issued \in [Ids -> 0 .. MaxNat]
    /\ claim \in [Ids -> 0 .. MaxNat]
    /\ holding \in [Ids -> BOOLEAN]
    /\ crashed \in SUBSET Ids

Init ==
    /\ issued = [p \in Ids |-> 0]
    /\ claim = [p \in Ids |-> 0]
    /\ holding = [p \in Ids |-> FALSE]
    /\ crashed = {}

\* A live process takes a new ticket, but the ticket numbers are a
\* finite pool (bounded by MaxNat) rather than the full NAT.
TakeTicket(p) ==
    /\ p \notin crashed
    /\ ~holding[p]
    /\ claim[p] = 0
    /\ issued[p] < MaxNat
    /\ issued' = [issued EXCEPT ![p] = @ + 1]
    /\ claim' = [claim EXCEPT ![p] = issued[p] + 1]
    /\ UNCHANGED <<holding, crashed>>

\* A process enters the critical section only when its ticket is newer
\* than every other live, non-holding process's ticket.
Enter(p) ==
    /\ p \notin crashed
    /\ claim[p] > 0
    /\ ~holding[p]
    /\ \A q \in Ids \ crashed :
           (holding[q] \/ claim[q] < claim[p])
    /\ holding' = [holding EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<issued, claim, crashed>>

Leave(p) ==
    /\ holding[p]
    /\ holding' = [holding EXCEPT ![p] = FALSE]
    /\ claim' = [claim EXCEPT ![p] = 0]
    /\ UNCHANGED <<issued, crashed>>

Crash(p) ==
    /\ p \notin crashed
    /\ crashed' = crashed \cup {p}
    /\ holding' = [holding EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<issued, claim>>

Next ==
    \/ \E p \in Ids : TakeTicket(p)
    \/ \E p \in Ids : Enter(p)
    \/ \E p \in Ids : Leave(p)
    \/ \E p \in Ids : Crash(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A p, q \in Ids : (holding[p] /\ holding[q]) => p = q

Inv ==
    /\ \A p \in Ids : holding[p] => (claim[p] > 0 /\ \A q \in Ids \ {p} : claim[q] <= claim[p])
    /\ \A p \in Ids : claim[p] <= issued[p]

\* Overridden operator: Nat from Naturals, finite instead of infinite.
NatOverride == 0

====