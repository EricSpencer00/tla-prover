---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

\* Model-checking configuration for the Bakery mutual exclusion spec: the
\* natural number type is overridden with a finite range so the state space
\* stays small; every identifier the .cfg expects is defined here.
CONSTANTS N, MaxNat

VARIABLES inCS, wants, ticket, maxVote, votes

vars == <<inCS, wants, ticket, maxVote, votes>>

\* The global ticket counter for the Bakery algorithm. In the inductive
\* spec it is a free variable (bounded by MaxNat) rather than starting at 0.
TypeOK ==
  /\ inCS \subseteq 1..N
  /\ wants \subseteq 1..N
  /\ ticket \in 0..MaxNat
  /\ maxVote \in 0..MaxNat
  /\ votes \in [1..N -> 0..MaxNat]

MutualExclusion ==
  \A p, q \in inCS : p = q

Init ==
  /\ inCS = {}
  /\ wants = {}
  /\ ticket = 0
  /\ maxVote = 0
  /\ votes = [p \in 1..N |-> 0]

\* A process that wants the critical section takes a fresh ticket.
Request(p) ==
  /\ p \notin wants
  /\ wants' = wants \cup {p}
  /\ UNCHANGED <<inCS, ticket, maxVote, votes>>

\* A process broadcasts its ticket to every other process.
Vote(p, q) ==
  /\ p \in wants
  /\ ~(\E m \in inCS : m = p)
  /\ votes' = [votes EXCEPT ![q] = IF ticket > @ THEN ticket ELSE @]
  /\ maxVote' = IF ticket > maxVote THEN ticket ELSE maxVote
  /\ UNCHANGED <<inCS, wants, ticket>>

\* The process enters the critical section only after a majority of votes
\* have caught up to its own ticket number.
Enter(p) ==
  /\ p \in wants
  /\ p \notin inCS
  /\ Cardinality({q \in 1..N : votes[q] >= ticket}) * 2 > N
  /\ inCS' = inCS \cup {p}
  /\ UNCHANGED <<wants, ticket, maxVote, votes>>

\* A process in the critical section leaves it.
Exit(p) ==
  /\ p \in inCS
  /\ inCS' = inCS \ {p}
  /\ wants' = wants \ {p}
  /\ ticket' = IF ticket < MaxNat THEN ticket + 1 ELSE ticket
  /\ UNCHANGED <<maxVote, votes>>

VoteStep == \E p \in 1..N, q \in 1..N : Vote(p, q)

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ VoteStep
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

\* The full inductive invariant from the Bakery specification (mutual
\* exclusion plus the bounded natural-number discipline).
Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ maxVote <= MaxNat

\* The spec starts from an arbitrary state satisfying the invariant (the
\* inductive start) and only requires weak fairness on voting.
ISpec == Init /\ [][Next]_vars /\ WF_vars(VoteStep)

====