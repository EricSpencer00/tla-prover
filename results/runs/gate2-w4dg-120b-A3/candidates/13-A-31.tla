---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* NatOverride replaces the infinite Nat from Naturals with a finite range
\* 0..MaxNat so the model is checkable. It is defined as an operator, not a
\* constant, and EXTENDS Naturals is kept so other operators are available.
NatOverride(n) == n \in 0..MaxNat

VARIABLES cs, ticket, number, choosing

vars == <<cs, ticket, number, choosing>>

\* A process is in the bakery when it is choosing a ticket or waiting.
InBakery(p) == choosing[p] \/ p \in cs

Init == /\ cs = {}
        /\ ticket = [p \in 1..N |-> 0]
        /\ number = 0
        /\ choosing = [p \in 1..N |-> FALSE]

\* Choose: a process not in the bakery starts choosing a ticket.
Choose(p) == /\ ~InBakery(p)
             /\ ~choosing[p]
             /\ choosing' = [choosing EXCEPT ![p] = TRUE]
             /\ UNCHANGED <<cs, ticket, number>>

\* TakeTicket: the choosing process takes the next ticket number, if finite.
TakeTicket(p) == /\ choosing[p]
                 /\ number < MaxNat
                 /\ ticket' = [ticket EXCEPT ![p] = number + 1]
                 /\ number' = number + 1
                 /\ choosing' = [choosing EXCEPT ![p] = FALSE]
                 /\ UNCHANGED cs

\* Enter: a process enters the critical section once its ticket is the
\* smallest among those not already in the critical section.
Enter(p) == /\ ~InBakery(p)
             /\ \A q \in cs : ticket[p] < ticket[q]
             /\ cs' = cs \cup {p}
             /\ UNCHANGED <<ticket, number, choosing>>

\* Exit: a process leaves the critical section.
Exit(p) == /\ p \in cs
           /\ cs' = cs \ {p}
           /\ UNCHANGED <<ticket, number, choosing>>

Next == \/ \E p \in 1..N : Choose(p)
        \/ \E p \in 1..N : TakeTicket(p)
        \/ \E p \in 1..N : Enter(p)
        \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars
ISpec == Spec /\ WF_vars(\E p \in 1..N : Choose(p))
                 /\ WF_vars(\E p \in 1..N : TakeTicket(p))
                 /\ WF_vars(\E p \in 1..N : Enter(p))
                 /\ WF_vars(\E p \in 1..N : Exit(p))

MutualExclusion == \A p, q \in cs : p = q

TypeOK == /\ cs \subseteq (1..N)
          /\ ticket \in [1..N -> 0..MaxNat]
          /\ number \in 0..MaxNat
          /\ choosing \in [1..N -> BOOLEAN]

Inv == /\ MutualExclusion
       /\ TypeOK
       /\ number = Cardinality({p \in 1..N : ticket[p] # 0})

====