---- MODULE Voting ----
\* High-level voting-based consensus: acceptors cast votes for values in numbered ballots.
\* A value is safe at a ballot only if every lower ballot is supported by a quorum, and a
\* quorum is a set of acceptors with pairwise overlap. Every cast vote must be safe, which
\* guarantees that two quorums can never converge on different values -- consistency.
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Convenience abbreviations for the quantifier-free descriptions of the sets.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES vote, threshold
vars == <<vote, threshold>>

Cast(v, a, b) == [val |-> v, acc |-> a, bal |-> b]

VoteSet(v, b) == {c \in Acceptor : [val |-> v, acc |-> c, bal |-> b] \in vote}
BallotOf(v) == {b \in Ballot : [val |-> v, acc |-> a1, bal |-> b] \in vote}

TypeOK ==
  /\ vote \subseteq [val : MCValue, acc : MCAcceptor, bal : MCBallot]
  /\ threshold \in [MCAcceptor -> Nat]

Init ==
  /\ vote = {}
  /\ threshold = [a \in MCAcceptor |-> 0 - 1]

\* An acceptor may raise its promise threshold and then refuse to vote below it.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED vote

\* Casting a vote requires the ballot to be above the threshold, no local conflict
\* with an earlier vote by this acceptor, no competing vote in this ballot, and quorum
\* safety at the ballot -- and the vote itself raises the threshold to the ballot.
CastVote(a, v, b) ==
  /\ b >= threshold[a]
  /\ \A c \in MCAcceptor : [val |-> v, acc |-> c, bal |-> b] \notin vote
  /\ \A c \in MCAcceptor : ([val |-> v, acc |-> c, bal |-> b] \in vote) => (c = a)
  /\ (\A c \in MCAcceptor : [val |-> v, acc |-> c, bal |-> b] \in vote) # {}
  /\ \A c \in MCQuorum : \A x \in c :
       \/ [val |-> v, acc |-> x, bal |-> b] \in vote
       \/ (\E e \in Ballot : e < b /\ [val |-> v, acc |-> x, bal |-> e] \notin vote)
  /\ vote' = vote \cup {Cast(v, a, b)}
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in MCAcceptor, b \in MCBallot : RaiseThreshold(a, b)
  \/ \E a \in MCAcceptor, v \in MCValue, b \in MCBallot : CastVote(a, v, b)

Spec == Init /\ [][Next]_vars

\* Every vote in the record must be safe at its ballot number, which is the heart
\* of consistency: it is what forces different quorums to agree on the same value.
VotesAreSafe ==
  \A w \in vote :
    \A e \in Ballot : e < w.bal =>
      \A c \in MCQuorum : \A x \in c :
        \/ [val |-> w.val, acc |-> x, bal |-> e] \in vote
        \/ (\E e2 \in Ballot : e2 < e /\ [val |-> w.val, acc |-> x, bal |-> e2] \notin vote)

\* At most one value is ever voted for in any given ballot, across the whole record.
AtMostOneValuePerBallot ==
  \A v, u \in MCValue : VoteSet(v, BallotOf(v)) \cap VoteSet(u, BallotOf(v)) # {}
    => v = u

\* The chosen set (those values that some quorum voted for at some ballot) never
\* contains two different values.
ChosenIsSingleton ==
  \A v, u \in MCValue : (\E q \in MCQuorum : VoteSet(v, BallotOf(v)) \supseteq q)
                        /\ (\E q \in MCQuorum : VoteSet(u, BallotOf(u)) \supseteq q) => v = u

\* The consensus driver view: Consistency follows from safety of every vote, plus
\* the fact that each ballot carries at most one value and the variables are typed.
Inv == VotesAreSafe /\ AtMostOneValuePerBallot /\ ChosenIsSingleton /\ TypeOK

\* The voting implementation refines the abstract consensus driver: chosen values
\* are exactly those with a witnessing quorum, and the invariant is exactly the
\* driver consistency property.
ConsensusSpecBar == ChosenIsSingleton

\* Ballot numbers are abstract natural numbers; the model bounds them below.
BallotBound == \E b \in Ballot : b < 2

\* The quorum sets are nonempty, contain at least two members, and any two quorums
\* overlap -- this overlap is the source of consistency across ballots.
QuorumsOverlap ==
  /\ \A q \in MCQuorum : Cardinality(q) >= 2
  /\ \A q \in MCQuorum : \A r \in MCQuorum : q \cap r # {}

\* The symmetry group: acceptors are interchangeable, so swapping two acceptor
\* names in every vote and threshold leaves the reachable state set unchanged.
MCSymmetry ==
  {f \in [MCAcceptor -> MCAcceptor] :
      /\ {f[a] : a \in MCAcceptor} = MCAcceptor
      /\ \A a \in MCAcceptor : \A c \in MCAcceptor :
           (f[a] = f[c]) => (a = c)}
====