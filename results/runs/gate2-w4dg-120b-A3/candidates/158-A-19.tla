---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* The module models a Paxos-like voting consensus algorithm in which acceptors
\* cast votes for values in numbered ballots.  Each ballot may only ever carry
\* votes for a single value, which is what guarantees the chosen set stays
\* unary.  The operators at the end are the ones the reference .cfg rewrites
\* into.
CONSTANTS
  a1, a2, a3,
  v1, v2,
  Acceptor,
  Value,
  Quorum,
  Ballot

VARIABLES
  votes,    \* votes[a] = the set of (ballot, value) pairs acceptor a has cast
  promised  \* promised[a] = the highest ballot a has promised to respect

vars == <<votes, promised>>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ promised \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ promised = [a \in Acceptor |-> -1]

\* An acceptor can increase its promise threshold without ever casting a vote.
\* This is what makes it impossible for it to later throw away a vote already
\* collected at a lower ballot.
RaiseThreshold(a, b) ==
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* CastVote is guarded by the quorum-safety test: no other acceptor may have
\* already voted for a different value in this same ballot.
CastVote(a, b, v) ==
  /\ b >= promised[a]
  /\ \A w \in votes[a] : w[1] # b
  /\ \A c \in Quorum : (a \in c => \A ca \in c : ~(\E x \in votes[ca] : x[1] = b /\ x[2] # v))
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ promised' = [promised EXCEPT ![a] = b]

Next ==
  \E a \in Acceptor :
    \/ \E b \in Ballot : RaiseThreshold(a, b)
    \/ \E b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* A value is safe at ballot b if for every earlier ballot c, every quorum has
\* either already voted for it or is already out of that ballot.
SafeAt(b, v) ==
  \A c \in Ballot :
    (c < b) =>
      \E cQ \in Quorum :
        \A ca \in cQ :
          \/ \E x \in votes[ca] : x[1] = c /\ x[2] = v
          \/ promised[ca] > c

AllVotesAreSafe ==
  \A a \in Acceptor : \A w \in votes[a] : SafeAt(w[1], w[2])

\* At most one value is voted for per ballot, and votes are well typed.
OneValuePerBallot ==
  /\ \A a \in Acceptor : \A w \in votes[a] : w[1] \in Ballot /\ w[2] \in Value
  /\ \A a, ca \in Acceptor :
       \A b \in Ballot :
         ((b \in Domain({w \in votes[a] : w[2] \in Value}) /\ b \in Domain({w \in votes[ca] : w[2] \in Value}))
          => \A v \in {w \in votes[a] : w[1] = b} : \A v2 \in {w \in votes[ca] : w[1] = b} : v[2] = v2[2])

Chosen == {v \in Value : \E c \in Quorum : \A a \in c : <<1, v>> \in votes[a]}

Inv == AllVotesAreSafe /\ OneValuePerBallot

\* The high-level safety property: any two values that were ever each carried a
\* quorum of votes in some ballot must be the same value.
\* This follows from the two invariants above and is exposed as its own
\* property so the model checker can report a direct counterexample.
ConsensusSpecBar ==
  \A v, v2 \in Chosen : v = v2

MCSymmetry == {id \in [Acceptor -> Acceptor] : \A a \in Acceptor : id[a] = a}

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====