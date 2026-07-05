---- MODULE VoteProof ----
EXTENDS Integers, NaturalsInduction, FiniteSets, FiniteSetTheorems, 
        WellFoundedInduction, TLC, TLAPS

CONSTANT Value,     \* As in module Consensus, the set of choosable values.
        Acceptor,  \* The set of all acceptors.
        Quorum     \* The set of all quorums.

ASSUME QA == /\ \A Q \in Quorum : Q \subseteq Acceptor
             /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
PROOF BY QA
============================================================================