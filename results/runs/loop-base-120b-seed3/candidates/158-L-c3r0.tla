---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

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
        \A a1, a2 \in Acceptor :
            \A p1 \in votes[a1] , p2 \in votes[a2] :
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
    /\ \A a2 \in Acceptor :
          \A p \in votes[a2] :
              (p.ballot = b) => p.value = v           \* no other value in same ballot
    /\ \E Q \in Quorum :
          \A a2 \in Q :
              ( \E p \in votes[a2] : p.ballot = b /\ p.value = v )
              \/ promise[a2] > b                       \* quorum witnesses safety
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
    /\ \A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2
    /\ UNION { {f[a]} : a \in Acceptor } = Acceptor

MCSymmetry == { f \in [Acceptor -> Acceptor] : IsPermutation(f) }

(*--------------------------------------------------------------------
  Consensus safety property (consistency)
--------------------------------------------------------------------*)
ConsensusSpecBar ==
    \A v1, v2 \in Value :
    \A b1, b2 \in Ballot :
    \A Q1, Q2 \in Quorum :
        ( (\A a \in Q1 :
                \E p \in votes[a] : p.ballot = b1 /\ p.value = v1) /\
          (\A a \in Q2 :
                \E p \in votes[a] : p.ballot = b2 /\ p.value = v2) )
        => v1 = v2

====