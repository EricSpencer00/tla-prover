---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Acceptor, \* Set of acceptor identifiers
    Value,    \* Set of possible values
    Quorum,   \* Set of quorums, each quorum is a subset of Acceptor
    Ballot    \* Set of ballot numbers (natural numbers)

(*-----------------------------------------------------------------
  Types
-----------------------------------------------------------------*)
Vote == [bal : Ballot, val : Value]

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES
    votes,      \* Map from each acceptor to the set of votes it has cast
    threshold   \* Map from each acceptor to its current promise threshold

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
(* No acceptor has voted in ballot b for a value different from v *)
SameValueInBallot(b, v) ==
    \A a \in Acceptor :
        \A w \in votes[a] :
            (w.bal = b) => (w.val = v)

(* There is at most one value voted for in ballot b across all acceptors *)
AtMostOneValuePerBallot(b) ==
    \A v1, v2 \in Value :
        ( \E a1 \in Acceptor : [bal |-> b, val |-> v1] \in votes[a1] ) /\
        ( \E a2 \in Acceptor : [bal |-> b, val |-> v2] \in votes[a2] )
        => v1 = v2

(* A quorum demonstrates that value v is safe at ballot b *)
SafeAt(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E q \in Quorum :
                \A a \in q :
                    ( [bal |-> c, val |-> v] \in votes[a] ) \/
                    ( threshold[a] > c )          \* a can never vote in c

(*-----------------------------------------------------------------
  Initial predicate
-----------------------------------------------------------------*)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
IncreaseThreshold(a, newBal) ==
    /\ a \in Acceptor
    /\ newBal \in Ballot
    /\ newBal > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = newBal]
    /\ UNCHANGED votes

Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= threshold[a]                      \* respects current promise
    /\ \A w \in votes[a] : w.bal # b          \* hasn't voted in this ballot yet
    /\ SameValueInBallot(b, v)                \* no other acceptor voted different
    /\ SafeAt(v, b)                           \* value is safe at this ballot
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[bal |-> b, val |-> v]}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, nb \in Ballot : IncreaseThreshold(a, nb)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<votes, threshold>>

(*-----------------------------------------------------------------
  Invariant required by the .cfg
-----------------------------------------------------------------*)
Inv ==
    /\ \A a \in Acceptor : \A w \in votes[a] : SafeAt(w.val, w.bal)
    /\ \A b \in Ballot : AtMostOneValuePerBallot(b)

(*-----------------------------------------------------------------
  Property required by the .cfg (consistency of chosen values)
-----------------------------------------------------------------*)
ChosenValues ==
    { v \in Value : \E b \in Ballot, q \in Quorum :
        \A a \in q : [bal |-> b, val |-> v] \in votes[a] }

ConsensusSpecBar ==
    Cardinality(ChosenValues) <= 1

=============================================================================