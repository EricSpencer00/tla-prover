---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

ASSUME N = 3

VARIABLES cs, ticket, nextTicket

vars == <<cs, ticket, nextTicket>>

TypeOK == /\ cs \subseteq (1..N)
          /\ ticket \in [1..N -> 0..MaxNat]
          /\ nextTicket \in 0..MaxNat

Init ==
  /\ cs = {}
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0

Request(p) ==
  /\ p \notin cs
  /\ ticket[p] = 0
  /\ nextTicket < MaxNat
  /\ nextTicket' = nextTicket + 1
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket + 1]
  /\ UNCHANGED cs

Enter(p) ==
  /\ p \notin cs
  /\ ticket[p] # 0
  /\ cs = {}
  /\ cs' = cs \cup {p}
  /\ UNCHANGED <<ticket, nextTicket>>

Exit(p) ==
  /\ p \in cs
  /\ cs' = cs \ {p}
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED nextTicket

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N : Request(p))
  /\ WF_vars(\E p \in 1..N : Enter(p))
  /\ WF_vars(\E p \in 1..N : Exit(p))

MutualExclusion == \A p \in cs : \A q \in cs : p = q

Inv == /\ cs \subseteq (1..N)
       /\ ticket \in [1..N -> 0..MaxNat]
       /\ nextTicket \in 0..MaxNat
       /\ \A p \in 1..N : p \in cs => ticket[p] < MaxNat

StateConstraint == \A p \in 1..N : ticket[p] <= MaxNat

====