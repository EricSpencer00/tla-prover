---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Override the standard Nat to be a finite range 0..MaxNat for model checking.
Nat(x) == IF x <= MaxNat THEN x ELSE 0

VARIABLES inCS, want, ticket, nextTicket

vars == <<inCS, want, ticket, nextTicket>>

TypeOK ==
    /\ inCS \subseteq 0..(N - 1)
    /\ want \subseteq 0..(N - 1)
    /\ ticket \in [0..(N - 1) -> 0..MaxNat]
    /\ nextTicket \in 0..(MaxNat + 1)

MutualExclusion == \A a, b \in inCS : a = b

Inv ==
    /\ TypeOK
    /\ MutualExclusion
    /\ \A p \in inCS : p \in want

Init ==
    /\ inCS = {}
    /\ want = {}
    /\ ticket = [p \in 0..(N - 1) |-> 0]
    /\ nextTicket = 0

Request(p) ==
    /\ p \notin want
    /\ want' = want \cup {p}
    /\ ticket' = [ticket EXCEPT ![p] = Nat(nextTicket)]
    /\ nextTicket' = Nat(nextTicket + 1)
    /\ UNCHANGED inCS

Enter(p) ==
    /\ p \in want
    /\ p \notin inCS
    /\ \A q \in want : ticket[p] <= ticket[q]
    /\ inCS' = inCS \cup {p}
    /\ want' = want \ {p}
    /\ UNCHANGED <<ticket, nextTicket>>

Exit(p) ==
    /\ p \in inCS
    /\ inCS' = inCS \ {p}
    /\ UNCHANGED <<want, ticket, nextTicket>>

Next ==
    \/ \E p \in 0..(N - 1) : Request(p)
    \/ \E p \in 0..(N - 1) : Enter(p)
    \/ \E p \in 0..(N - 1) : Exit(p)

Spec == Init /\ [][Next]_vars

ISpec == Spec /\ WF_vars(Exit(0)) /\ WF_vars(Exit(1))
====