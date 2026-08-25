---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\*  Basic assumptions about the constants
\* ----------------------------------------------------------------------
ASSUME a1 # a2 /\ a1 # a3 /\ a2 # a3
ASSUME v1 # v2
ASSUME Acceptor = {a1, a2, a3}
ASSUME Value    = {v1, v2}
ASSUME Ballot \subseteq Nat
ASSUME \A q \in Quorum : q \subseteq Acceptor
ASSUME \A q1, q2 \in Quorum : q1 # {} /\ q2 # {} => (q1 \cap q2) # {}

\* ----------------------------------------------------------------------
\*  Operators substituted by the model checker
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\*  State variables
\* ----------------------------------------------------------------------
VARIABLES votes, promise

\* votes[a] is the set of votes cast by acceptor a.
\* Each vote is a record [ballot : Ballot, value : Value].
VoteRecord == [ballot : Ballot, value : Value]

\* promise[a] is the smallest ballot number a will ever vote in
\* (initialized to -1, meaning no promise).
\* We model -1 as a special element not in Nat.
\* For simplicity we treat it as an integer.
\* Note: the model checker will bound Ballot, so -1 is outside that range.
\* ----------------------------------------------------------------------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ promise = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\*  Safety predicate: a value v is safe at ballot b
\* ----------------------------------------------------------------------
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E q \in Quorum :
                \A a \in q :
                    ( \E vt \in votes[a] :
                        /\ vt.ballot = c
                        /\ vt.value = v )
                    \/ (promise[a] > c)

\* ----------------------------------------------------------------------
\*  Action: increase promise threshold without voting
\* ----------------------------------------------------------------------
PromiseInc(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > promise[a]
    /\ promise' = [promise EXCEPT ![a] = b]
    /\ UNCHANGED votes

\* ----------------------------------------------------------------------
\*  Action: cast a vote for value v in ballot b
\* ----------------------------------------------------------------------
Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= promise[a]                     \* respects current promise
    /\ ~(\E vt \in votes[a] : vt.ballot = b)   \* hasn't voted in b yet
    /\ \A a2 \in Acceptor :
          \A vt2 \in votes[a2] :
              (vt2.ballot = b) => (vt2.value = v)   \* no conflicting vote
    /\ Safe(v, b)                           \* value is safe
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {{ballot |-> b, value |-> v}}]
    /\ promise' = [promise EXCEPT ![a] = b]

\* ----------------------------------------------------------------------
\*  Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E a \in Acceptor, b \in Ballot : PromiseInc(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, promise>>

\* ----------------------------------------------------------------------
\*  Helper definitions for invariants
\* ----------------------------------------------------------------------
AllVotes ==
    { vt : \E a \in Acceptor : vt \in votes[a] }

VoteBallots ==
    { vt.ballot : vt \in AllVotes }

\* At most one value per ballot across all acceptors
OneValuePerBallot ==
    \A b \in VoteBallots :
        \A vt1, vt2 \in AllVotes :
            /\ vt1.ballot = b
            /\ vt2.ballot = b
        => vt1.value = vt2.value

\* Every vote is safe at its ballot
AllVotesSafe ==
    \A a \in Acceptor :
        \A vt \in votes[a] :
            Safe(vt.value, vt.ballot)

\* Type correctness (already enforced by definition, but stated explicitly)
TypeOK ==
    /\ votes \in [Acceptor -> SUBSET VoteRecord]
    /\ promise \in [Acceptor -> Int]   \* Int allows -1

\* ----------------------------------------------------------------------
\*  Invariant
\* ----------------------------------------------------------------------
Inv == TypeOK /\ AllVotesSafe /\ OneValuePerBallot

\* ----------------------------------------------------------------------
\*  Definition of the chosen values set
\* ----------------------------------------------------------------------
ChosenValues ==
    { v \in Value :
        \E b \in Ballot, q \in Quorum :
            /\ \A a \in q :
                \E vt \in votes[a] :
                    /\ vt.ballot = b
                    /\ vt.value = v }

\* ----------------------------------------------------------------------
\*  Consensus safety property: at most one value is ever chosen
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (v1 \in ChosenValues /\ v2 \in ChosenValues) => v1 = v2

\* ----------------------------------------------------------------------
\*  Symmetry: all permutations of acceptors
\* ----------------------------------------------------------------------
IsBijective(f) ==
    /\ \A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2
    /\ \A a \in Acceptor : \E a0 \in Acceptor : f[a0] = a

MCSymmetry == { f \in [Acceptor -> Acceptor] : IsBijective(f) }

====