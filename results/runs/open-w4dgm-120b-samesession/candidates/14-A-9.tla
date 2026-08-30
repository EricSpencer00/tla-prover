---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, MaxNat

VARIABLES phase, requester, inCS, ticket, nextTicket, queue

vars == <<phase, requester, inCS, ticket, nextTicket, queue>>

Phases == {"idle", "waiting", "cs"}

Range(s) == {s[i] : i \in DOMAIN s}

TypeOK ==
  /\ phase \in [1..N -> Phases]
  /\ requester \in 1..N
  /\ inCS \subseteq 1..N
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ queue \in Seq(1..N)

Init ==
  /\ phase = [i \in 1..N |-> "idle"]
  /\ requester = 1
  /\ inCS = {}
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ queue = << >>

Enqueue(i) ==
  /\ phase[i] = "idle"
  /\ ~\E k \in DOMAIN queue : queue[k] = i
  /\ queue' = Append(queue, i)
  /\ UNCHANGED <<phase, requester, inCS, ticket, nextTicket>>

Enter(i) ==
  /\ queue # << >>
  /\ Head(queue) = i
  /\ phase[i] = "idle"
  /\ nextTicket < MaxNat
  /\ inCS = {}
  /\ phase' = [phase EXCEPT ![i] = "cs"]
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ queue' = Tail(queue)
  /\ UNCHANGED <<requester, inCS>>

Leave(i) ==
  /\ phase[i] = "cs"
  /\ phase' = [phase EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<requester, inCS, ticket, nextTicket, queue>>

Next ==
  \E i \in 1..N : Enqueue(i) \/ Enter(i) \/ Leave(i)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A i \in 1..N : phase[i] = "cs" => inCS = {}

Inv ==
  /\ \A i \in 1..N : phase[i] = "cs" => ticket[i] < nextTicket
  /\ \A i \in 1..N : phase[i] = "cs" => inCS = {}
  /\ \A i \in 1..N : phase[i] = "idle" => ticket[i] = 0
  /\ \A i \in 1..N : phase[i] = "waiting" => ticket[i] = 0

TicketBound == \A i \in 1..N : ticket[i] < MaxNat

====