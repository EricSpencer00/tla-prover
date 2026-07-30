---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

VARIABLES active, waiting, served, ticket, nextTicket
vars == << active, waiting, served, ticket, nextTicket >>

TypeOK ==
  /\ active \in 0..MaxNat
  /\ waiting \in 0..MaxNat
  /\ served \in 0..MaxNat
  /\ ticket \in [0..N-1 -> Nat]
  /\ nextTicket \in Nat

MutualExclusion ==
  \A a \in 0..N-1, b \in 0..N-1 :
     (a # b /\ ticket[a] = ticket[b]) => (active = 0)

Init ==
  /\ active = 0
  /\ waiting = 0
  /\ served = 0
  /\ ticket = [i \in 0..N-1 |-> 0]
  /\ nextTicket = 0

Arrive ==
  /\ waiting < MaxNat
  /\ waiting' = waiting + 1
  /\ UNCHANGED << active, served, ticket, nextTicket >>

TakeTicket(i) ==
  /\ waiting > 0
  /\ active = 0
  /\ nextTicket # MaxNat
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ active' = i + 1
  /\ waiting' = waiting - 1
  /\ UNCHANGED served

Release(i) ==
  /\ active = i + 1
  /\ served < MaxNat
  /\ served' = served + 1
  /\ active' = 0
  /\ UNCHANGED << waiting, ticket, nextTicket >>

Next ==
  \/ Arrive
  \/ \E i \in 0..N-1 : TakeTicket(i)
  \/ \E i \in 0..N-1 : Release(i)

Spec == Init /\ [][Next]_vars

NatBound ==
  \A i \in 0..N-1 : ticket[i] < MaxNat

Inv == MutualExclusion /\ TypeOK

====