---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, TLC

(*--------------------------------------------------------------------
  CONSTANTS (to be instantiated in the .cfg file)
--------------------------------------------------------------------*)
CONSTANT a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(*--------------------------------------------------------------------
  Substitution operators for the model checker
--------------------------------------------------------------------*)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES votes, promise

(*--------------------------------------------------------------------
  Type definitions
--------------------------------------------------------------------*)
TypeOK ==
    /\ votes \in [Acceptor -> SUBSET [ballot : Ballot, value : Value]]
    /\ promise \in [Acceptor -> Int]  \* allows the initial -1

(*--------------------------------------------------------------------
  Safety predicate for a vote (b,v)
--------------------------------------------------------------------*)
Safe(b, v) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( \E p \in votes[a] : p.ballot = c /\ p.value = v )
                    \/ promise[a] > c

(*--------------------------------------------------------------------
  Invariant that every cast vote is safe
--------------------------------------------------------------------*)
AllVotesSafe ==
    \A a \in Acceptor :
        \A p \in votes[a] :
            Safe(p.ballot, p.value)

(*--------------------------------------------------------------------
  At most one value per ballot across all acceptors
--------------------------------------------------------------------*)
AtMostOneValuePerBallot ==
    \A b \in Ballot :
        \A a \in Acceptor :
            \A a2b \in Acceptor :
                \A p1 \in votes[a] , p2 \in votes[a2b] :
                    (p1.ballot = b /\ p2.ballot = b) => p1.value = p2.value

(*--------------------------------------------------------------------
  The overall invariant
--------------------------------------------------------------------*)
Inv == TypeOK /\ AllVotesSafe /\ AtMostOneValuePerBallot

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ promise = [a \in Acceptor |-> -1]

(*--------------------------------------------------------------------
  Action: increase promise threshold without voting
--------------------------------------------------------------------*)
PromiseIncrease(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > promise[a]
    /\ UNCHANGED votes
    /\ promise' = [promise EXCEPT ![a] = b]

(*--------------------------------------------------------------------
  Action: cast a vote for value v in ballot b
--------------------------------------------------------------------*)
Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= promise[a]                                 \* not below current promise
    /\ ~(\E p \in votes[a] : p.ballot = b)            \* not voted in this ballot yet
    /\ \A a2b \in Acceptor :
          \A p \in votes[a2b] :
              (p.ballot = b) => p.value = v           \* no other value in same ballot
    /\ \E Q \in Quorum :
          \A a2b \in Q :
              ( \E p \in votes[a2b] : p.ballot = b /\ p.value = v )
              \/ promise[a2b] > b                       \* quorum witnesses safety
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ promise' = [promise EXCEPT ![a] = b]

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ \E a \in Acceptor : \E b \in Ballot : PromiseIncrease(a, b)
    \/ \E a \in Acceptor : \E b \in Ballot : \E v \in Value : Vote(a, b, v)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<votes, promise>>

(*--------------------------------------------------------------------
  Symmetry set: all permutations of Acceptor
--------------------------------------------------------------------*)
IsPermutation(f) ==
    /\ f \in [Acceptor -> Acceptor]
    /\ \A x, y \in Acceptor : f[x] = f[y] => x = y
    /\ UNION { {f[x]} : x \in Acceptor } = Acceptor

MCSymmetry == { f \in [Acceptor -> Acceptor] : IsPermutation(f) }

(*--------------------------------------------------------------------
  Consensus safety property (consistency)
--------------------------------------------------------------------*)
ConsensusSpecBar ==
    \A vA \in Value :
    \A vB \in Value :
    \A bA \in Ballot :
    \A bB \in Ballot :
    \A Q1 \in Quorum :
    \A Q2 \in Quorum :
        ( (\A a \in Q1 :
                \E p \in votes[a] : p.ballot = bA /\ p.value = vA) /\
          (\A a \in Q2 :
                \E p \in votes[a] : p.ballot = bB /\ p.value = vB) )
        => vA = vB

====