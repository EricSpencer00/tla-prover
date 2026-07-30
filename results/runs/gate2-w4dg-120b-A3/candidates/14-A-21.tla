---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Ticket numbers are taken from a finite range for model checking.  The
\* operator that does the overriding is NatOverride (not Nat); EXTENDS
\* Naturals stays in force, but Nat is never DECLARED here.
NatOverride == MaxNat + 1

VARIABLES pc, turn, ticket, pc2, turn2, ticket2

vars == <<pc, turn, ticket, pc2, turn2, ticket2>>

Init ==
  /\ pc = 0
  /\ turn = MaxNat
  /\ ticket = 0
  /\ pc2 = 0
  /\ turn2 = MaxNat
  /\ ticket2 = 0

\* All Boulanger actions are inherited unchanged; the state constraint below
\* is what keeps ticket numbers in the finite range.
Next ==
  \/ \E i \in 0..(N - 1) :
       /\ pc = 0
       /\ pc' = 1
       /\ turn' = turn
       /\ ticket' = ticket
       /\ pc2' = pc2
       /\ turn2' = turn2
       /\ ticket2' = ticket2
  \/ \E i \in 0..(N - 1) :
       /\ pc = 1
       /\ turn' = i
       /\ ticket' = ticket + 1
       /\ pc' = 2
       /\ pc2' = pc2
       /\ turn2' = turn2
       /\ ticket2' = ticket2
  \/ \E i \in 0..(N - 1) :
       /\ pc = 2
       /\ turn = i
       /\ pc' = 3
       /\ pc2' = pc2
       /\ turn2' = turn2
       /\ ticket2' = ticket2
  \/ pc = 3
       /\ pc' = 0
       /\ turn' = turn
       /\ ticket' = ticket
       /\ pc2' = pc2
       /\ turn2' = turn2
       /\ ticket2' = ticket2
  \/ \E i \in 0..(N - 1) :
       /\ pc2 = 0
       /\ pc2' = 1
       /\ turn2' = turn2
       /\ ticket2' = ticket2
       /\ pc' = pc
       /\ turn' = turn
       /\ ticket' = ticket
  \/ \E i \in 0..(N - 1) :
       /\ pc2 = 1
       /\ turn2' = i
       /\ ticket2' = ticket2 + 1
       /\ pc2' = 2
       /\ pc' = pc
       /\ turn' = turn
       /\ ticket' = ticket
  \/ \E i \in 0..(N - 1) :
       /\ pc2 = 2
       /\ turn2 = i
       /\ pc2' = 3
       /\ pc' = pc
       /\ turn' = turn
       /\ ticket' = ticket
       /\ ticket2' = ticket2
  \/ pc2 = 3
       /\ pc2' = 0
       /\ turn2' = turn2
       /\ ticket2' = ticket2
       /\ pc' = pc
       /\ turn' = turn
       /\ ticket' = ticket

\* Ticket numbers must stay below the finite bound; this is the only thing
\* that differs from the unbounded Boulanger specification.
TicketBound ==
  /\ ticket < MaxNat
  /\ ticket2 < MaxNat

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i \in 0..(N - 1) :
    (pc = 2 /\ turn = i) => (pc2 # 2 \/ turn2 # i)

TypeOK ==
  /\ pc \in 0..3
  /\ turn \in 0..(N - 1)
  /\ ticket \in 0..MaxNat
  /\ pc2 \in 0..3
  /\ turn2 \in 0..(N - 1)
  /\ ticket2 \in 0..MaxNat

Inv ==
  /\ MutualExclusion
  /\ TypeOK

====