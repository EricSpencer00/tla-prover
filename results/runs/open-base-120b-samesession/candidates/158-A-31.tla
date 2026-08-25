---- MODULE Voting ----
EXTENDS Naturals, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* concrete bounds used by the model checker
MCAcceptor == {a1, a2, a3}
MCValue    == {v1, v2}
MCQuorum   == {{a1, a2}, {a1, a3}, {a2, a3}}
MCBallot   == 0..2

VARIABLES Votes, Thresh

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ Votes = [a \in Acceptor |-> {}]
    /\ Thresh = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
PromiseAction ==
    \E a \in Acceptor: \E b \in Ballot:
        /\ b > Thresh[a]                \* raise promise
        /\ Votes' = Votes
        /\ Thresh' = [Thresh EXCEPT ![a] = b]

VoteAction ==
    \E a \in Acceptor: \E b \in Ballot: \E v \in Value:
        /\ b >= Thresh[a]                                   \* respect promise
        /\ ~(\E w \in Votes[a] : w.ballot = b)               \* not voted in b yet
        /\ \A a2 \in Acceptor :
               (a2 # a) => 
               \A w \in Votes[a2] :
                    (w.ballot = b) => (w.value = v)          \* no conflicting vote
        /\ \E Q \in Quorum:
               /\ \A a2 \in Q:
                     ( (\E w \in Votes[a2] : w.ballot = b /\ w.value = v)
                       \/ (Thresh[a2] > b) )                \* quorum safety
        /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup { [ballot |-> b, value |-> v] }]
        /\ Thresh' = [Thresh EXCEPT ![a] = b]

Next == \/ PromiseAction \/ VoteAction

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<Votes, Thresh>>

\* ----------------------------------------------------------------------
\* Type invariant
TypeInv ==
    /\ Votes \in [Acceptor -> SUBSET {[ballot: Ballot, value: Value]}]
    /\ Thresh \in [Acceptor -> Int]

\* ----------------------------------------------------------------------
\* Safety of a single vote
SafeVote(vote) ==
    LET b   == vote.ballot
        val == vote.value
    IN
    \A c \in 0..(b-1):
        \E Q \in Quorum:
            /\ \A a \in Q:
                 ( (\E w \in Votes[a] : w.ballot = c /\ w.value = val)
                   \/ (Thresh[a] > c) )

AllVotesSafe ==
    \A a \in Acceptor: \A w \in Votes[a] : SafeVote(w)

\* ----------------------------------------------------------------------
\* At most one value per ballot
OneValuePerBallot ==
    \A a1, a2 \in Acceptor:
        \A w1 \in Votes[a1]:
            \A w2 \in Votes[a2]:
                (w1.ballot = w2.ballot) => (w1.value = w2.value)

\* ----------------------------------------------------------------------
\* Global invariant
Inv == TypeInv /\ AllVotesSafe /\ OneValuePerBallot

\* ----------------------------------------------------------------------
\* Definition of a chosen value
ChosenValue(v) ==
    \E b \in Ballot: \E Q \in Quorum:
        /\ \A a \in Q: \E w \in Votes[a] : w.ballot = b /\ w.value = v

\* ----------------------------------------------------------------------
\* Consensus property (at most one value ever chosen)
ConsensusSpecBar == [] ( \A v1, v2 \in Value :
                         (ChosenValue(v1) /\ ChosenValue(v2)) => v1 = v2 )

\* ----------------------------------------------------------------------
\* Symmetry set (identity permutation – sufficient for the checker)
MCSymmetry == { [a \in Acceptor |-> a] }

====