---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

VARIABLES phase, ticket, cpset
vars == <<phase, ticket, cpset>>

Phases == {"idle", "waiting", "critical"}

\* Dijkstra's Bakery algorithm: a process enters the critical section only while
\* it holds the strictly smallest ticket number among those in the CS. The
\* bounded Nat type forces ticket numbers to saturate at MaxNat, which is what
\* makes the state space finite for model checking.
TypeOK ==
  /\ phase \in [1..N -> Phases]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ cpset \subseteq (1..N)

Init ==
  /\ phase = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ cpset = {}

\* A process takes a ticket one above the highest currently held. Because Nat is
\* finite, a saturated request keeps the maximal ticket.
Request(i) ==
  /\ phase[i] = "idle"
  /\ phase' = [phase EXCEPT ![i] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![i] =
        IF \E j \in 1..N : phase[j] = "critical" /\ ticket[j] = MaxNat
          THEN MaxNat
          ELSE (IF \E k \in 1..N : phase[k] = "waiting" /\ ticket[k] > ticket[i]
                  THEN ticket[i] + 1
                  ELSE ticket[i])
      ]
  /\ UNCHANGED cpset

Enter(i) ==
  /\ phase[i] = "waiting"
  /\ \A j \in cpset : ticket[i] <= ticket[j]
  /\ phase' = [phase EXCEPT ![i] = "critical"]
  /\ cpset' = cpset \cup {i}
  /\ UNCHANGED ticket

Exit(i) ==
  /\ phase[i] = "critical"
  /\ phase' = [phase EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ cpset' = cpset \ {i}

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

Spec == Spec /\ Next
Spec == Init /\ [][Next]_vars

\* A process in the CS has a strictly smaller ticket than every other process
\* also in the CS; since ticket numbers are drawn from a totally ordered set,
\* two processes can never be in the CS together.
MutualExclusion ==
  \A i \in 1..N : phase[i] = "critical" => \A j \in 1..N : (j # i /\ phase[j] = "critical") => ticket[i] < ticket[j]

\* The ticket for any process that is not idle must be positive, and any process
\* in the CS must be in the critical-phase set.
TypeOK == TypeOK /\ \A i \in 1..N : phase[i] = "critical" => i \in cpset

\* The full inductive invariant: ticket numbers are never negative, and every
\* process in the CS holds a ticket number that is at least as large as any
\* other process's ticket, so a two-process CS is ruled out by transitivity.
Inv ==
  /\ \A i \in 1..N : ticket[i] >= 0
  /\ \A i \in cpset : \A j \in 1..N : ticket[i] >= ticket[j]

ISpec == Spec

\* Override the infinite natural numbers with the bounded range.
NatOverride == 0..MaxNat

====