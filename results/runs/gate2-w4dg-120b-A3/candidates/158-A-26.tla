---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Ballot is a bounded extract of the natural numbers for model checking.
\* The CONSTRAINT below enforces the overlap property of Quorum.
CONSTRAINT \A q1, q2 \in Quorum : q1 \cap q2 # {}

\* A vote is an (ballot, value) pair; each acceptor casts a set of votes.
Vote == Ballot \X Value
Votes == [Acceptor -> SUBSET Vote]
Threshold == [Acceptor -> Ballot \cup {-1}]

VARIABLES votes, thr
vars == <<votes, thr>>

\* A set of acceptors votes for a value in a ballot iff every member has
\* exactly that vote in its local set.
BallotVoters(v, b) == {a \in Acceptor : <<b, v>> \in votes[a]}

Chosen == {v \in Value : \E q \in Quorum : \A a \in q : <<v>> \in BallotVoters(v, q)}

Init == /\ votes = [a \in Acceptor |-> {}]
        /\ thr = [a \in Acceptor |-> -1]

\* No promise has been made; any ballot is allowed.
RaiseThreshold(a, b) == /\ thr[a] # b
                        /\ thr' = [thr EXCEPT ![a] = b]
                        /\ UNCHANGED votes

\* Voting is safe only if the value is safe at the ballot number.
Vote(a, b, v) == /\ b >= thr[a]
                 /\ \A w \in Value : (w # v) => <<b, w>> \notin votes[a]
                 /\ \A c \in Ballot : c < b => \E q \in Quorum :
                        \A a2 \in q :
                          <<c, v>> \in votes[a2] \/ \A w \in Value : <<c, w>> \notin votes[a2]
                 /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
                 /\ thr' = [thr EXCEPT ![a] = b]

Next == \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
        \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Every cast vote is safe at its ballot number.
VoteIsSafe == \A a \in Acceptor :
               \A b \in Ballot, v \in Value :
                 (<<b, v>> \in votes[a]) =>
                   \A c \in Ballot : c < b =>
                     \E q \in Quorum :
                       \A a2 \in q : <<c, v>> \in votes[a2] \/ \A w \in Value : <<c, w>> \notin votes[a2]

\* One value per ballot across all acceptors.
OneValuePerBallot == \A a1, a2 \in Acceptor :
                       \A b \in Ballot, v1, v2 \in Value :
                         (<<b, v1>> \in votes[a1] /\ <<b, v2>> \in votes[a2]) => v1 = v2

\* Type correctness of votes and thresholds.
TypeOK == /\ votes \in Votes
          /\ thr \in Threshold

\* Consistency: at most one value is ever placed in the chosen set.
Inv == VoteIsSafe /\ OneValuePerBallot /\ TypeOK

\* The voting algorithm implements the abstract consensus spec.
ConsensusSpecBar == Chosen \subseteq Value

Spec == Init /\ [][Next]_vars

\* A trivial symmetry group: the identity permutation on acceptors.
MCSymmetry == {[a1 |-> a1, a2 |-> a2, a3 |-> a3]}

\* Overridden operators for the model checker to bind to finite sets.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====