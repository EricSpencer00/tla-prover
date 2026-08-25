---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANT a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Substitution operators for the model checker
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, threshold

\* ---------- Helper definitions ----------
VoteRecord == [ballot : Ballot, value : Value]

\* Type correctness invariant
TypeInv ==
    /\ votes \in [Acceptor -> SUBSET VoteRecord]
    /\ threshold \in [Acceptor -> Int]

\* The set of values that have been voted for in a given ballot
ValsInBallot(b) ==
    { v \in Value :
        \E a \in Acceptor :
            \E vr \in votes[a] : vr.ballot = b /\ vr.value = v }

\* At most one value per ballot across all acceptors
AtMostOnePerBallot ==
    \A b \in Ballot :
        Cardinality( ValsInBallot(b) ) <= 1

\* Safety of a single vote (the vote must be safe at its ballot)
SafeVote(vr) ==
    \A c \in Ballot :
        (c < vr.ballot) => 
            \E Q \in Quorum :
                \A a \in Q :
                    ( \E vr2 \in votes[a] :
                          vr2.ballot = c /\ vr2.value = vr.value )
                    \/ threshold[a] > c

SafeVotes ==
    \A a \in Acceptor :
        \A vr \in votes[a] : SafeVote(vr)

\* ---------- Actions ----------
Raise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= threshold[a]                     \* not below promise
    /\ \A vr \in votes[a] : vr.ballot # b   \* not already voted in this ballot
    /\ \A a2 \in Acceptor :
          \A vr2 \in votes[a2] :
              (vr2.ballot = b) => vr2.value = v   \* no other value in same ballot
    /\ \E Q \in Quorum :
          \A a2 \in Q :
              ( \E vr2 \in votes[a2] :
                    vr2.ballot = b /\ vr2.value = v )
              \/ threshold[a2] > b                \* can never vote in b
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot : Raise(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

\* ---------- Initialization ----------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<votes, threshold>>

\* ---------- Invariant ----------
Inv == /\ TypeInv
       /\ AtMostOnePerBallot
       /\ SafeVotes

\* ---------- Chosen values ----------
Chosen(v) ==
    \E b \in Ballot, Q \in Quorum :
        \A a \in Q :
            \E vr \in votes[a] :
                vr.ballot = b /\ vr.value = v

\* ---------- Property (consistency) ----------
ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (Chosen(v1) /\ Chosen(v2)) => v1 = v2

\* ---------- Symmetry ----------
MCSymmetry ==
    { p \in [Acceptor -> Acceptor] :
        \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2 }

====