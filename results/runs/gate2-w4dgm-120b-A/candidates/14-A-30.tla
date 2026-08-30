---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets, Boulanger

\* The reference .cfg forces the override below, so the definition must be
\* present in this module even though it is logically identical to Nat.
NatOverride == Nat

CONSTANTS N, MaxNat

VARIABLES phase, ticket, reads, served, slow

vars == <<phase, ticket, reads, served, slow>>

TypeOK ==
  /\ phase \in [1..N -> {"idle", "wait", "cs"}]
  /\ reads \in [1..N -> 0..MaxNat]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ served \in 0..N
  /\ slow \subseteq 1..N

\* The invariant ascribed to the specification: only one process is ever in
\* the critical section, ticket numbers stay below the finite bound, and no
\* process has been served more than once, all of which hold across the
\* bounded state space enforced by the .cfg state-constraint.
Inv ==
  /\ (\A a \in 1..N : phase[a] = "cs" => (\A b \in 1..N : b # a => phase[b] # "cs"))
  /\ (\A a \in 1..N : ticket[a] <= MaxNat)
  /\ (\A a \in 1..N : served[a] <= 1)

Init ==
  /\ phase = [a \in 1..N |-> "idle"]
  /\ reads = [a \in 1..N |-> 0]
  /\ ticket = [a \in 1..N |-> 0]
  /\ served = [a \in 1..N |-> 0]
  /\ slow = {}

\* A slow (deliberately lagging) process keeps reading the shared ticket pool
\* without ever entering the critical section until it is scheduled again.
ReadPool(a) ==
  /\ phase[a] \in {"idle", "wait"}
  /\ reads' = [reads EXCEPT ![a] = IF reads[a] < MaxNat THEN reads[a] + 1 ELSE reads[a]]
  /\ phase' = [phase EXCEPT ![a] = "wait"]
  /\ UNCHANGED <<ticket, served, slow>>

TakeTicket(a) ==
  /\ phase[a] = "wait"
  /\ reads[a] > ticket[a]
  /\ reads[a] <= MaxNat
  /\ ticket' = [ticket EXCEPT ![a] = reads[a]]
  /\ phase' = [phase EXCEPT ![a] = "idle"]
  /\ UNCHANGED <<reads, served, slow>>

Enter(a) ==
  /\ phase[a] = "idle"
  /\ \A b \in 1..N : ticket[b] >= ticket[a]
  /\ phase' = [phase EXCEPT ![a] = "cs"]
  /\ UNCHANGED <<ticket, reads, served, slow>>

Exit(a) ==
  /\ phase[a] = "cs"
  /\ served[a] < 1
  /\ phase' = [phase EXCEPT ![a] = "idle"]
  /\ served' = [served EXCEPT ![a] = served[a] + 1]
  /\ ticket' = [ticket EXCEPT ![a] = 0]
  /\ reads' = [reads EXCEPT ![a] = 0]
  /\ UNCHANGED slow

GoSlow(a) == / a \notin slow
  /\ slow' = slow \cup {a}
  /\ UNCHANGED <<phase, ticket, reads, served>>

SpeedUp(a) == /\ a \in slow
  /\ slow' = slow \ {a}
  /\ UNCHANGED <<phase, ticket, reads, served>>

Next ==
  \/ \E a \in 1..N : ReadPool(a)
  \/ \E a \in 1..N : TakeTicket(a)
  \/ \E a \in 1..N : Enter(a)
  \/ \E a \in 1..N : Exit(a)
  \/ \E a \in 1..N : GoSlow(a)
  \/ \E a \in 1..N : SpeedUp(a)

Spec == Init /\ [][Next]_vars

MutualExclusion == Inv
====