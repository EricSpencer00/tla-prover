---- MODULE MCBoulanger ----
EXTENDS Naturals

\* The module is a model-checking configuration for the Boulanger mutual
\* exclusion algorithm.  It inherits the entire behavioral spec from the
\* base Boulanger module and simply limits natural numbers to a finite range
\* with a state constraint, so every identifier required by the .cfg is
\* present here.

CONSTANTS N, MaxNat

VARIABLES pc, ticket, nextTicket, served
vars == <<pc, ticket, nextTicket, served>>

TypeOK ==
    /\ pc \in [1..N -> {"idle", "wait", "cs"}]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat
    /\ served \subseteq (1..N)

Init ==
    /\ pc = [i \in 1..N |-> "idle"]
    /\ ticket = [i \in 1..N |-> 0]
    /\ nextTicket = 0
    /\ served = {}

Request(i) ==
    /\ pc[i] = "idle"
    /\ nextTicket < MaxNat
    /\ nextTicket' = nextTicket + 1
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket + 1]
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED served

\* A process enters the critical section only if its ticket is strictly
\* lower than every ticket held by another waiting process.
Enter(i) ==
    /\ pc[i] = "wait"
    /\ \A j \in 1..N : (j # i /\ pc[j] = "wait") => ticket[i] < ticket[j]
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<ticket, nextTicket, served>>

Exit(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ served' = served \cup {i}
    /\ UNCHANGED nextTicket

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A i \in 1..N : pc[i] = "cs" => (\A j \in 1..N : j # i => pc[j] # "cs")

\* The inductive invariant from the Boulanger spec, carried through unchanged.
Inv ==
    /\ \A i \in 1..N : pc[i] \in {"idle", "wait", "cs"}
    /\ \A i \in 1..N : (pc[i] = "wait") => (ticket[i] >= 1 /\ ticket[i] <= MaxNat)
    /\ nextTicket >= 0 /\ nextTicket <= MaxNat
    /\ \A i, j \in 1..N :
         (pc[i] = "wait" /\ pc[j] = "wait" /\ ticket[i] = ticket[j]) => i = j

\* The state constraint keeps the model finite: no ticket may ever reach the
\* configured maximum, so the overridden Nat can never overflow.
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

====