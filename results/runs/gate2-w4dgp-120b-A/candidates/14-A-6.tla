---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, nextTicket, wait
vars == <<inCS, ticket, nextTicket, wait>>

NatOverride == 0..MaxNat

TypeOK ==
  /\ inCS \in 0..(N - 1)
  /\ ticket \in [0..(N - 1) -> NatOverride]
  /\ nextTicket \in NatOverride
  /\ wait \in SUBSET (0..(N - 1))

Inv ==
  /\ inCS \in 0..(N - 1)
  /\ ticket \in [0..(N - 1) -> NatOverride]
  /\ nextTicket \in NatOverride
  /\ wait \in SUBSET (0..(N - 1))

MutualExclusion ==
  /\ \A i \in wait : ticket[i] < nextTicket
  /\ inCS \notin wait
  /\ nextTicket > 0 => ticket[inCS] < nextTicket

Init ==
  /\ inCS = 0
  /\ ticket = [i \in 0..(N - 1) |-> 0]
  /\ nextTicket = 0
  /\ wait = {}

Request(i) ==
  /\ nextTicket < MaxNat
  /\ i \notin wait
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ wait' = wait \cup {i}
  /\ UNCHANGED inCS

Enter(i) ==
  /\ i \in wait
  /\ (\A j \in wait : ticket[i] <= ticket[j])
  /\ inCS' = i
  /\ wait' = wait \ {i}
  /\ UNCHANGED <<ticket, nextTicket>>

Leave ==
  /\ inCS' = 0
  /\ UNCHANGED <<ticket, nextTicket, wait>>

Next ==
  \/ \E i \in 0..(N - 1) : Request(i)
  \/ \E i \in 0..(N - 1) : Enter(i)
  \/ Leave

Spec == Init /\ [][Next]_vars

NatBound ==
  /\ nextTicket <= MaxNat
  /\ \A i \in 0..(N - 1) : ticket[i] <= MaxNat
====