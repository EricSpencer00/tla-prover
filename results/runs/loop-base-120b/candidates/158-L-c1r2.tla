---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\*-------------------------------------------------
\* Substituted constants (bounded versions)
\*-------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\*-------------------------------------------------
\* State variables
\*-------------------------------------------------
VARIABLES votes, thresh

\* votes[a] is the set of (ballot,value) pairs already cast by acceptor a
\* thresh[a] is the current promise threshold of acceptor a
\*-------------------------------------------------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

\*-------------------------------------------------
\* Safety predicate
\*-------------------------------------------------
SafeAt(b, v) ==
    /\ b \in Ballot
    /\ v \in Value
    /\ \A c \in Ballot :
          (c < b) =>
            \E Q \in Quorum :
                /\ \A a \in Q :
                       (<<c, v>> \in votes[a]) \/ (thresh[a] > c)

\*-------------------------------------------------
\* Action: raise promise threshold
\*-------------------------------------------------
Promise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > thresh[a]
    /\ thresh' = [thresh EXCEPT ![a] = b]
    /\ votes'  = votes

\*-------------------------------------------------
\* Action: cast a vote
\*-------------------------------------------------
Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= thresh[a]               \* not below current promise
    /\ <<b, v>> \notin votes[a]     \* not already voted in this ballot
    /\ \A a2p \in Acceptor :
          \A vv \in Value :
              (<<b, vv>> \in votes[a2p]) => vv = v   \* unanimity in ballot b
    /\ SafeAt(b, v)                 \* value is safe at this ballot
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
    /\ thresh' = [thresh EXCEPT ![a] = b]

\*-------------------------------------------------
\* Next-state relation
\*-------------------------------------------------
Next ==
    \E a \in Acceptor, b \in Ballot :
        \/ Promise(a, b)
        \/ (\E v \in Value : Vote(a, b, v))

\*-------------------------------------------------
\* Specification
\*-------------------------------------------------
Spec ==
    Init /\ [][Next]_<<votes, thresh>>

\*-------------------------------------------------
\* Definition of chosen values
\*-------------------------------------------------
Chosen(v) ==
    /\ v \in Value
    /\ \E b \in Ballot :
          \E Q \in Quorum :
              /\ \A a \in Q : <<b, v>> \in votes[a]

\*-------------------------------------------------
\* Invariant components
\*-------------------------------------------------
\* (a) Every vote is safe at its ballot
Inv1 ==
    /\ \A a \in Acceptor :
          \A vt \in votes[a] :
              SafeAt(vt[1], vt[2])

\* (b) At most one value per ballot across all acceptors
Inv2 ==
    /\ \A b \in Ballot :
          /\ \A aA, aB \in Acceptor :
              /\ \A vv1, vv2 \in Value :
                  (<<b, vv1>> \in votes[aA] /\ <<b, vv2>> \in votes[aB]) => vv1 = vv2

\* (c) Type correctness of state variables
Inv3 ==
    /\ \A a \in Acceptor :
          /\ thresh[a] \in Int
          /\ votes[a] \subseteq { <<b, v>> : b \in Ballot, v \in Value }

Inv == Inv1 /\ Inv2 /\ Inv3

\*-------------------------------------------------
\* Safety property: at most one chosen value
\*-------------------------------------------------
ConsensusSpecBar ==
    /\ \A w1, w2 \in Value :
          (Chosen(w1) /\ Chosen(w2)) => w1 = w2

\*-------------------------------------------------
\* Symmetry definition (identity permutation)
\*-------------------------------------------------
MCSymmetry ==
    { [a \in Acceptor |-> a] }

====