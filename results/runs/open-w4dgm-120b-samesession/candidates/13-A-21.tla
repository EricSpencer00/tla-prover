---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES inCS, interested, ticket, served, nextTicket

vars == <<inCS, interested, ticket, served, nextTicket>>

RECURSIVE SumServed(_)
SumServed(k) == IF k = 0 THEN 0 ELSE served[k] + SumServed(k - 1)

Init == /\ inCS = [p \in 1..N |-> FALSE]
        /\ interested = [p \in 1..N |-> FALSE]
        /\ ticket = [p \in 1..N |-> 0]
        /\ served = [p \in 1..N |-> 0]
        /\ nextTicket = 1

Request(p) == /\ ~interested[p]
              /\ ~inCS[p]
              /\ nextTicket <= MaxNat
              /\ interested' = [interested EXCEPT ![p] = TRUE]
              /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
              /\ nextTicket' = nextTicket + 1
              /\ UNCHANGED <<inCS, served>>

Enter(p) == /\ interested[p]
            /\ \A q \in 1..N : ~inCS[q]
            /\ inCS' = [inCS EXCEPT ![p] = TRUE]
            /\ UNCHANGED <<interested, ticket, served, nextTicket>>

Exit(p) == /\ inCS[p]
           /\ inCS' = [inCS EXCEPT ![p] = FALSE]
           /\ interested' = [interested EXCEPT ![p] = FALSE]
           /\ served' = [served EXCEPT ![p] = @ + 1]
           /\ UNCHANGED <<ticket, nextTicket>>

Next == \E p \in 1..N : Request(p) \/ Enter(p) \/ Exit(p)

ISpec == Init /\ [][Next]_vars

MutualExclusion == \A p \in 1..N : inCS[p] => (\A q \in 1..N : (q # p) => ~inCS[q])

TypeOK == /\ inCS \in [1..N -> BOOLEAN]
          /\ interested \in [1..N -> BOOLEAN]
          /\ ticket \in [1..N -> 0..MaxNat]
          /\ served \in [1..N -> 0..MaxNat]
          /\ nextTicket \in 1..(MaxNat + 1)

Inv == SumServed(N) <= MaxNat

NatOverride == Nat
====