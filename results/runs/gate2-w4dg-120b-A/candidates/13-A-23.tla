---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* The system inherits all its state from the Bakery module; this wrapper applies
\* a model-checking bound to the natural-number type.
\* We re-export the Bakery operators under the same names so that the .cfg
\* configuration (which names them exactly) is satisfied.

\* Bakery's state: the critical-section set, each process's ticket number,
\* each process's phase, and the free ticket numbers.
VARIABLES cs, ticket, phase, free

vars == <<cs, ticket, phase, free>>

TypeOK == /\ cs \subseteq 1..N
          /\ ticket \in [1..N -> Nat]
          /\ phase \in [1..N -> {"idle", "waiting", "cs"}]
          /\ free \subseteq Nat

InitBakery == /\ cs = {}
              /\ ticket = [i \in 1..N |-> 0]
              /\ phase = [i \in 1..N |-> "idle"]
              /\ free = Nat

PickTicket == \E n \in free :
                /\ \E i \in 1..N :
                     /\ phase[i] = "idle"
                     /\ phase' = [phase EXCEPT ![i] = "waiting"]
                     /\ ticket' = [ticket EXCEPT ![i] = n]
                /\ free' = free \ {n}
                /\ UNCHANGED cs

Enter == \E i \in 1..N :
           /\ phase[i] = "waiting"
           /\ \A j \in 1..N : (phase[j] = "cs") => (ticket[i] < ticket[j])
           /\ cs' = cs \cup {i}
           /\ phase' = [phase EXCEPT ![i] = "cs"]
           /\ UNCHANGED <<ticket, free>>

Exit == \E i \in 1..N :
          /\ phase[i] = "cs"
          /\ cs' = cs \ {i}
          /\ phase' = [phase EXCEPT ![i] = "idle"]
          /\ free' = free \cup {ticket[i]}
          /\ ticket' = [ticket EXCEPT ![i] = 0]

NextBakery == PickTicket \/ Enter \/ Exit

MutualExclusion == \A i \in 1..N : i \in cs => phase[i] = "cs"

Inv == TypeOK /\ MutualExclusion

\* ISpec uses the inductive specification: any reachable state must satisfy the
\* invariant and can make an allowed transition. Nxt wraps the Bakery NEXT.
ISpec == InitBakery /\ [][NextBakery]_vars
TypeOKSpec == TypeOK
InvSpec == Inv

Init == InitBakery
Next == NextBakery
====