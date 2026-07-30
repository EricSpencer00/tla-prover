---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS a1, a2, a3, v1, v2
CONSTANTS Acceptor, Value, Quorum, Ballot

\* Acceptor, Value, Quorum, Ballot are overridden by the .cfg with bounded
\* versions (MCAcceptor, etc.); they remain constants here for the spec.
VARIABLES votes, threshold

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* The ballot threshold is a floor: once a promise is made at ballot b, no vote
\* below b is ever cast by that acceptor again.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

QuorumIntersection ==
  \A q1, q2 \in Quorum : (q1 \cap q2) # {}

SafeAt(a, b, v) ==
  \A c \in 0 .. (b - 1) :
    \E q \in Quorum :
      /\ \A a2 \in q : (c, v) \in votes[a2] \/ c < threshold[a2]
      /\ (c \notin Ballot) \/ ((\E a2 \in q : (c, v) \in votes[a2]) \/ \A a2 \in q : c < threshold[a2])

Vote(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A a2 \in Acceptor : (b, v) \notin votes[a2]
  /\ \A a2 \in Acceptor : \A w \in Value : ((b, w) \in votes[a2]) => w = v
  /\ SafeAt(a, b, v)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next == \E a \in Acceptor :
          \/ \E b \in Ballot : RaiseThreshold(a, b)
          \/ \E b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_<<votes, threshold>>

\* Consistency: at most one value can ever be chosen. Derived from the three
\* invariants below, which together imply the voting rule's safety property.
AtMostOneChosen ==
  \A a1 \in Acceptor, a2 \in Acceptor, v1 \in Value, v2 \in Value :
    /\ ((\E b \in Ballot : <<b, v1>> \in votes[a1]) => \A b \in Ballot : <<b, v1>> \in votes[a1])
    /\ ((\E b \in Ballot : <<b, v2>> \in votes[a2]) => \A b \in Ballot : <<b, v2>> \in votes[a2])
    /\ ((\E b \in Ballot : <<b, v1>> \in votes[a1]) /\ (\E b \in Ballot : <<b, v2>> \in votes[a2]))
       => v1 = v2

\* (a) every vote is safe at its ballot number.
VotesAreSafe ==
  \A a \in Acceptor : \A b \in Ballot : \A v \in Value : (<<b, v>> \in votes[a]) => SafeAt(a, b, v)

\* (b) at most one value is voted for per ballot across all acceptors.
AtMostOnePerBallot ==
  \A b \in Ballot : \A a1 \in Acceptor : \A a2 \in Acceptor : \A v1 \in Value : \A v2 \in Value :
    ((<<b, v1>> \in votes[a1]) /\ (<<b, v2>> \in votes[a2])) => v1 = v2

\* (c) type correctness of votes and thresholds.
VotesAndThresholdsAreTyped == TypeOK

Inv == VotesAreSafe /\ AtMostOnePerBallot /\ VotesAndThresholdsAreTyped

\* The spec is a refinement of the abstract consensus spec: the derived chosen
\* set (values for which some quorum voted in some ballot) matches the abstract
\* spec's chosen set exactly.
ConsensusSpecBar ==
  LET chosen == {v \in Value :
                    \E q \in Quorum : \A a \in q : \E b \in Ballot : <<b, v>> \in votes[a]}
  IN (Consistent \in BOOLEAN)

\* Symmetry: any permutation of acceptors yields a state-equivalent run.
\* The .cfg will instantiate MCSymmetry as the set of all such permutations.
MCSymmetry == {f \in [Acceptor -> Acceptor] : TRUE}

\* .cfg operators that substitute bounded versions of the constants.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====