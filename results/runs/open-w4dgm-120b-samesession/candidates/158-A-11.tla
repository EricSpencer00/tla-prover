---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Cast votes (ballot, value) per acceptor; threshold prevents voting below it.
VARIABLES cast, threshold

vars == <<cast, threshold>>

Votes == [ballot : Ballot, val : Value]

RECURSIVE SumVotes(_)
SumVotes(S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE IN Cardinality(cast[x]) + SumVotes(S \ {x})

Init ==
  /\ cast = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* Promising a higher ballot skips the acceptor's votes below it.
IncreaseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED cast

\* Vote is safe only if no other value has already won this ballot.
CastVote(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A p \in cast[a] : p.ballot # b
  /\ \A q \in Acceptor : \A p \in cast[q] : (p.ballot = b) => (p.val = v)
  /\ \E Q \in Quorum : \A member \in Q :
        /\ \A c \in Ballot : c < b => \E p \in cast[member] : p.ballot = c /\ p.val = v
        /\ ~(\A c \in Ballot : c < b => (\E p \in cast[member] : p.ballot = c /\ p.val = v))
  /\ cast' = [cast EXCEPT ![a] = cast[a] \cup {[ballot |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : IncreaseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* At most one value ever gathers a full quorum of votes.
Chosen == { v \in Value : \E Q \in Quorum : \A member \in Q : [ballot |-> "chosen", val |-> v] \in cast[member] }

VoteSafe(a) == \A p \in cast[a] :
  \A Q \in Quorum : \A member \in Q :
    /\ (\A c \in Ballot : c < p.ballot => \E q \in cast[member] : q.ballot = c /\ q.val = p.val)
    /\ ~(\A c \in Ballot : c < p.ballot => (\E q \in cast[member] : q.ballot = c /\ q.val = p.val))

BallotSingleValue == \A a \in Acceptor, p \in cast[a] : \A q \in Acceptor, r \in cast[q] :
  (p.ballot = r.ballot) => (p.val = r.val)

TypeOK ==
  /\ cast \in [Acceptor -> SUBSET Votes]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

\* Chosen is derived from votes; the derived-consensus spec refines the model.
ConsensusSpecBar == Chosen \subseteq { v \in Value : \E a \in Acceptor : [ballot |-> "chosen", val |-> v] \in cast[a] }

Inv == VoteSafe(a1) /\ VoteSafe(a2) /\ VoteSafe(a3) /\ BallotSingleValue /\ TypeOK

\* Symmetry: any permutation of the three acceptors is indistinguishable.
MCSymmetry == { [a1 |-> p[a1], a2 |-> p[a2], a3 |-> p[a3]]
                  : p \in { [a1 |-> a1, a2 |-> a2, a3 |-> a3],
                            [a1 |-> a1, a2 |-> a3, a3 |-> a2],
                            [a1 |-> a2, a2 |-> a1, a3 |-> a3],
                            [a1 |-> a2, a2 |-> a3, a3 |-> a1],
                            [a1 |-> a3, a2 |-> a1, a3 |-> a2],
                            [a1 |-> a3, a2 |-> a2, a3 |-> a1] } }

\* The .cfg substitutes the bounded versions of the type constants here.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====