---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\*-------------------------------------------------
\*  Operators used for model checking substitution
\*-------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\*-------------------------------------------------
\*  State variables
\*-------------------------------------------------
VARIABLES votes, threshold

vars == << votes, threshold >>

\* each acceptor's set of votes (each vote is a record [ballot, value])
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\*-------------------------------------------------
\*  Safety predicate for a value at a given ballot
\*-------------------------------------------------
Safe(b, v) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( \E vt \in votes[a] :
                         /\ vt.ballot = c
                         /\ vt.value  = v )
                    \/ threshold[a] > c

\*-------------------------------------------------
\*  Promise action (increase promise threshold)
\*-------------------------------------------------
Promise ==
    \E a \in Acceptor :
        \E b \in Ballot :
            /\ b > threshold[a]
            /\ threshold' = [threshold EXCEPT ![a] = b]
            /\ UNCHANGED votes

\*-------------------------------------------------
\*  Vote action (cast a vote for a value in a ballot)
\*-------------------------------------------------
Vote ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= threshold[a]                     \* not below current promise
                /\ ~(\E vt \in votes[a] : vt.ballot = b) \* no prior vote in this ballot
                /\ \A a2 \in Acceptor :
                       (\E vt2 \in votes[a2] : vt2.ballot = b) =>
                           (\A vt2 \in votes[a2] :
                               (vt2.ballot = b) => vt2.value = v)
                /\ Safe(b, v)                            \* value is safe at this ballot
                /\ votes' = [votes EXCEPT ![a] = votes[a] \cup
                               {[ballot |-> b, value |-> v]}]
                /\ threshold' = [threshold EXCEPT ![a] = b]
                /\ UNCHANGED << >>

\*-------------------------------------------------
\*  Next-state relation
\*-------------------------------------------------
Next == \/ Promise \/ Vote

\*-------------------------------------------------
\*  Specification
\*-------------------------------------------------
Spec == Init /\ [][Next]_vars

\*-------------------------------------------------
\*  Invariants
\*-------------------------------------------------
\* (1) Every recorded vote is safe
VoteSafe ==
    \A a \in Acceptor :
        \A vt \in votes[a] :
            Safe(vt.ballot, vt.value)

\* (2) At most one value per ballot across all acceptors
OneValuePerBallot ==
    \A b \in Ballot :
        ( \E v \in Value :
                \E a \in Acceptor :
                    \E vt \in votes[a] :
                        /\ vt.ballot = b
                        /\ vt.value  = v )
        => ( \A a' \in Acceptor :
                \A vt' \in votes[a'] :
                    (vt'.ballot = b) => vt'.value = v )

\* (3) Thresholds are either -1 or a ballot number
ThresholdBound ==
    \A a \in Acceptor :
        threshold[a] = -1 \/ threshold[a] \in Ballot

Inv == VoteSafe /\ OneValuePerBallot /\ ThresholdBound

\*-------------------------------------------------
\*  Definition of "chosen" value
\*-------------------------------------------------
Chosen(v) ==
    \E b \in Ballot :
        \E Q \in Quorum :
            \A a \in Q :
                \E vt \in votes[a] :
                    /\ vt.ballot = b
                    /\ vt.value  = v

\*-------------------------------------------------
\*  Consensus safety property
\*-------------------------------------------------
ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (Chosen(v1) /\ Chosen(v2)) => v1 = v2

\*-------------------------------------------------
\*  Symmetry definition (permutations of Acceptor)
\*-------------------------------------------------
IsPermutation(f) ==
    /\ \A a \in Acceptor : f[a] \in Acceptor
    /\ \A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2
    /\ \A b \in Acceptor : \E a \in Acceptor : f[a] = b

MCSymmetry == { f \in [Acceptor -> Acceptor] : IsPermutation(f) }

\*-------------------------------------------------
\*  Assumptions about constants
\*-------------------------------------------------
ASSUME Ballot \subseteq Nat
ASSUME Quorum \subseteq SUBSET Acceptor
ASSUME QuorumOverlap == \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

====