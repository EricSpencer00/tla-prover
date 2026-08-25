---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

(*--------------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(*--------------------------------------------------------------------
  Operators that the .cfg file substitutes for the above constants
--------------------------------------------------------------------*)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

(*--------------------------------------------------------------------
  Basic assumptions about the constants
--------------------------------------------------------------------*)
ASSUME /\ a1 \in Acceptor /\ a2 \in Acceptor /\ a3 \in Acceptor
       /\ a1 # a2 /\ a2 # a3 /\ a1 # a3
       /\ v1 \in Value /\ v2 \in Value /\ v1 # v2
       /\ \A Q \in Quorum : Q \subseteq Acceptor /\ Q # {}
       /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

(*--------------------------------------------------------------------
  Types
--------------------------------------------------------------------*)
Vote == [ballot : Ballot, value : Value]

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES votes, promise

Vars == <<votes, promise>>

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ votes = [a \in Acceptor |-> {}]                 \* each acceptor starts with no votes
    /\ promise = [a \in Acceptor |-> -1]                \* -1 means “no promise made”

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
\* An acceptor a has already voted in ballot b
HasVoted(a, b) == \E v \in Value : <<b, v>> \in votes[a]

\* The value (if any) that acceptor a voted for in ballot b
VoteValue(a, b) == 
    CHOOSE v \in Value : <<b, v>> \in votes[a]

\* Safety of a (ballot,value) pair
SafeAt(b, val) ==
    \A c \in Ballot :
        (c < b) =>
            (\E Q \in Quorum :
                \A a \in Q :
                    (<<c, val>> \in votes[a]) \/ promise[a] > c)

\* There is at most one value voted for in a given ballot across all acceptors
OneValuePerBallot ==
    \A b \in Ballot :
        \A v1, v2 \in Value :
            ( (\E a1 \in Acceptor : <<b, v1>> \in votes[a1]) /\ 
              (\E a2 \in Acceptor : <<b, v2>> \in votes[a2]) ) => v1 = v2

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
PromiseIncrease(a, newB) ==
    /\ a \in Acceptor
    /\ newB \in Ballot
    /\ newB > promise[a]                     \* must increase the threshold
    /\ promise' = [promise EXCEPT ![a] = newB]
    /\ UNCHANGED votes

VoteAction(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= promise[a]                       \* cannot vote below current promise
    /\ ~HasVoted(a, b)                       \* a has not voted in this ballot yet
    /\ \A a2 \in Acceptor :
          (a2 = a) \/ 
          ( (~HasVoted(a2, b)) \/ (VoteValue(a2, b) = v) )
    /\ \E Q \in Quorum :
          \A a2 \in Q :
              (<<b, v>> \in votes[a2]) \/ promise[a2] > b
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
    /\ promise' = [promise EXCEPT ![a] = b]

AcceptAction ==
    \E a \in Acceptor :
        ( \E newB \in Ballot :
            PromiseIncrease(a, newB)
        )
        \/ ( \E b \in Ballot, v \in Value :
                VoteAction(a, b, v)
           )

Next == AcceptAction

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_Vars

(*--------------------------------------------------------------------
  Invariant
--------------------------------------------------------------------*)
Inv ==
    /\ \A a \in Acceptor :
          \A vote \in votes[a] :
              /\ vote \in Vote
              /\ SafeAt(vote.ballot, vote.value)
    /\ OneValuePerBallot

(*--------------------------------------------------------------------
  Consistency property (at most one chosen value)
--------------------------------------------------------------------*)
ChosenValues ==
    { v \in Value :
        \E b \in Ballot, Q \in Quorum :
            \A a \in Q : <<b, v>> \in votes[a] }

ConsensusSpecBar == 
    \A v1, v2 \in ChosenValues : v1 = v2

(*--------------------------------------------------------------------
  Symmetry definition (set of permutations over Acceptor)
--------------------------------------------------------------------*)
MCSymmetry == { [a \in Acceptor |-> a] }

====