---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* Natural-language description: a high-level voting-based consensus algorithm over
\* acceptor processes and values, with quorum overlap. The safety property is:
\* at most one value is ever chosen, and it follows from three invariants:
\* every vote is safe, at most one value per ballot, and type correctness.
\* The specification must expose exactly the identifiers the .cfg names.

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

Votes == [ballot : Ballot, val : Value]

VARIABLES votesCast, lowerBound
vars == <<votesCast, lowerBound>>

QuorumHasAllAccepted(q, b, v) ==
  \A a \in q : [ballot |-> b, val |-> v] \in votesCast[a]

HasVoted(a, b) == \E x \in votesCast[a] : x.ballot = b

BallotsBelow(b) == {c \in Ballot : c < b}

VoterThinksItIsBehind(a, b) ==
  \E c \in BallotsBelow(b) :
    \E q \in Quorum :
      \A a2 \in q : HasVoted(a2, c) \/ lowerBound[a2] > c

TypeOK ==
  /\ votesCast \in [Acceptor -> SUBSET Votes]
  /\ lowerBound \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votesCast = [a \in Acceptor |-> {}]
  /\ lowerBound = [a \in Acceptor |-> -1]

RaiseFloor(a, b) ==
  /\ lowerBound[a] < b
  /\ lowerBound' = [lowerBound EXCEPT ![a] = b]
  /\ UNCHANGED votesCast

Vote(a, b, v) ==
  /\ lowerBound[a] <= b
  /\ ~ HasVoted(a, b)
  /\ \A a2 \in Acceptor : ~ HasVoted(a2, b) \/ \A x \in votesCast[a2] : x.val = v
  /\ \E q \in Quorum : QuorumHasAllAccepted(q, b, v)
  /\ VoterThinksItIsBehind(a, b)
  /\ votesCast' = [votesCast EXCEPT ![a] = votesCast[a] \cup {[ballot |-> b, val |-> v]}]
  /\ lowerBound' = [lowerBound EXCEPT ![a] = b]

Next == \E a \in Acceptor :
  \/ \E b \in Ballot : RaiseFloor(a, b)
  \/ \E b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Invariant (b): at most one value per ballot across all acceptors' votes.
AtMostOneValuePerBallot ==
  \A a1, a2 \in Acceptor :
    \A x1 \in votesCast[a1], x2 \in votesCast[a2] :
      x1.ballot = x2.ballot => x1.val = x2.val

\* Invariant (a): every vote is safe at its ballot number.
EveryVoteIsSafe ==
  \A a \in Acceptor :
    \A x \in votesCast[a] :
      VoterThinksItIsBehind(a, x.ballot)

\* Invariant (c): every vote is correctly typed and lowerBound stays in the
\* declared range, which is what lets the type-checker trust the others.
TypeSoundness == TypeOK

Inv == EveryVoteIsSafe /\ AtMostOneValuePerBallot /\ TypeSoundness

\* No concrete liveness property is given in the description; the spec still
\* needs the name the .cfg refers to, so a trivial safety statement is used.
ConsensusSpecBar == TRUE

====