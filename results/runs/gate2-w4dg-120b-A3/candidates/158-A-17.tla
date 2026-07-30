---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* The set of ballot numbers is the natural numbers, bounded in model checking.
Ballot == Nat

\* The model's participant sets are declared as constants in the .cfg, so they are
\* introduced here exactly as named.
CONSTANTS Acceptor, Value, Quorum

AcceptorSet == Acceptor
ValueSet == Value
QuorumSet == Quorum

VARIABLES votes, threshold

vars == <<votes, threshold>>

VotePairs == [ballot: Ballot, value: ValueSet]
NoVote == [ballot |-> 0, value |-> CHOOSE v \in ValueSet : TRUE]

TypeOK ==
    /\ votes \in [AcceptorSet -> SUBSET VotePairs]
    /\ threshold \in [AcceptorSet -> Nat \cup {-1}]

Init ==
    /\ votes = [a \in AcceptorSet |-> {}]
    /\ threshold = [a \in AcceptorSet |-> -1]

\* Raising the threshold freezes the acceptor out of ballots below it.
RaiseThreshold(a, b) ==
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

SafeAt(a, b, v) ==
    /\ \A c \in 0 .. (b - 1) :
         \E q \in QuorumSet :
           /\ \A x \in q : b \in votes[x].ballot
           /\ votes[x].value = v
    /\ \A other \in AcceptorSet :
         (a # other /\ b \in votes[other].ballot) => (votes[other].value = v)

\* Voting carries the same preconditions on the ballot as the messages it
\* abstracts over: it must be above the acceptor's threshold, and it must be the
\* first vote in that ballot by anybody, so the chosen set cannot split.
Vote(a, b, v) ==
    /\ b >= threshold[a]
    /\ \A other \in AcceptorSet : b \notin votes[other].ballot
    /\ SafeAt(a, b, v)
    /\ votes' = [votes EXCEPT ![a] = @ \cup {[ballot |-> b, value |-> v]}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in AcceptorSet, b \in Ballot : RaiseThreshold(a, b)
    \/ \E a \in AcceptorSet, b \in Ballot, v \in ValueSet : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* No two values can ever both be shown to have a quorum decision behind them.
Inv ==
    /\ \A a \in AcceptorSet : votes[a] \subseteq VotePairs
    /\ \A a \in AcceptorSet : \A p \in votes[a] : SafeAt(a, p.ballot, p.value)
    /\ \A a, b \in AcceptorSet : \A p \in votes[a] : \A q \in votes[b] : (p.ballot = q.ballot) => (p.value = q.value)

\* Refinement: the voting algorithm implements the abstract consensus spec
\* by mapping the chosen set to the set of values any quorum voted for.
ConsensusSpecBar == \A q \in QuorumSet : \E v \in ValueSet : \A x \in q : [ballot |-> 0, value |-> v] \in votes[x]

\* Any permutation of the acceptors that respects the quorum overlap is a
\* symmetry of the model; it is not exported, so the .cfg names it.
MCSymmetry == {f \in [AcceptorSet -> AcceptorSet] : \A q \in QuorumSet : f[q] \in QuorumSet}

\* The .cfg does not take the constants directly but the operators below, which
\* let a bounded model check a slice of the infinite ballot space.
MCAcceptor == AcceptorSet
MCValue == ValueSet
MCQuorum == QuorumSet
MCBallot == 0 .. 2

====