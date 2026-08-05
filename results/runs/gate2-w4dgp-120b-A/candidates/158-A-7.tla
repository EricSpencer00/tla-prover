---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* A voting-based consensus algorithm: acceptors vote for a value in numbered ballots,
\* and a value is chosen only if a quorum of acceptors has voted for it. Two different
\* values can never both reach a quorum in any ballot. The spec is a high-level,
\* message-free abstraction of Paxos (it does not model proposers or the network).
\* The invariant is that at most one value is ever chosen by a quorum of votes.

CONSTANTS Acceptor, Value, Quorum, Ballot

\* Safety: a vote is only cast for a value that is safe at that ballot number (no
\* conflicting vote can already exist in a lower ballot). ConsensusSpecBar is
\* defined below as the abstract consensus property; it refines to the concrete
\* chosen set (derived from the votes) by the refinement mapping at the end.
VARIABLES votes, threshold

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> (-1 :> Ballot)]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor may promise now to never vote in a ballot below n.
Raise ==
  { /\ \E a \in Acceptor, n \in Ballot :
        /\ n > threshold[a]
        /\ threshold' = [threshold EXCEPT ![a] = n]
    /\ UNCHANGED votes }

\* An acceptor votes for a value in a ballot, but only if the ballot is above its
\* promise threshold and the value is safe at that ballot (no conflicting lower
\* ballot vote can already exist).
Commit ==
  { /\ \E a \in Acceptor, n \in Ballot, v \in Value :
        /\ n >= threshold[a]
        /\ \A m \in Ballot : (n, v) \notin votes[a] \/ m < n
        /\ \A a2 \in Acceptor : \A m \in Ballot : (m, v) \in votes[a2] => m = n
        /\ \E q \in Quorum :
             \A d \in q : \E w \in Value : (n, w) \in votes[d] \/ (\E c \in Ballot : c < n /\ \A e \in q : (c, w) \in votes[e])
        /\ votes' = [votes EXCEPT ![a] = @ \cup {<<n, v>>}]
        /\ threshold' = [threshold EXCEPT ![a] = n]
    /\ UNCHANGED threshold }

Next == Raise \union Commit

Spec == Init /\ [][Next]_<<votes, threshold>>

\* A quorum for value v in ballot n is at least one quorum in which every member
\* has voted for v in that ballot, or can never vote in that ballot (is already
\* promised above it).
Quorums(v, n) ==
  { q \in Quorum : \A a \in q : (n, v) \in votes[a] \/ (\E m \in Ballot : m < n /\ (m, v) \in votes[a]) }

Chosen == { v \in Value : \E n \in Ballot : Quorums(v, n) # {} }

Inv ==
  /\ \A a \in Acceptor : \A n \in Ballot : \A v \in Value :
       (<<n, v>> \in votes[a] => (\A c \in Ballot : c < n => Quorums(v, c) # {}))
  /\ \A n \in Ballot : \A v1, v2 \in Value :
       ((Quorums(v1, n) # {} /\ Quorums(v2, n) # {}) => v1 = v2)
  /\ TypeOK

\* ConsensusSpecBar is the abstract property this algorithm implements: at most one
\* value is ever chosen by a quorum of votes. The refinement mapping below maps the
\* concrete chosen set from votes to the abstract chosen set.
ConsensusSpecBar == Cardinality(Chosen) <= 1

\* Symmetry: acceptors are interchangeable, so any permutation of them yields
\* an equivalent reachable state -- this keeps the state space small under
\* symmetry reduction in the model checker.
MCSymmetry == { f \in [Acceptor -> Acceptor] : [a \in Acceptor |-> votes[f[a]]] \in {votes} }
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

\* The concrete chosen set (from votes) implements the abstract chosen set from the
\* generic consensus spec.
SpecRefine == Spec /\ (Chosen = { v \in MCValue : \E n \in MCBallot : \E q \in MCQuorum : \A a \in q : <<n, v>> \in votes[a] })

====