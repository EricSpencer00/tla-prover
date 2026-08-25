---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, Sequences

(***************************************************************************)
(*  CONSTANTS                                                            *)
(***************************************************************************)
CONSTANTS 
    a1, a2, a3,               \* individual acceptors
    v1, v2,                   \* individual values
    Acceptor,                 \* set of all acceptors
    Value,                    \* set of all values
    Quorum,                   \* set of quorums (each a subset of Acceptor)
    Ballot                    \* set of ballot numbers (natural numbers)

(***************************************************************************)
(*  Operators that the .cfg file may replace                               *)
(***************************************************************************)
MCAcceptor == { a1, a2, a3 }
MCValue    == { v1, v2 }
MCQuorum   == { {a1, a2}, {a2, a3}, {a1, a3} }  \* example quorums, all intersect
MCBallot   == 0..2                               \* example bounded ballot set

(***************************************************************************)
(*  State variables                                                       *)
(***************************************************************************)
VARIABLES votes, threshold

(***************************************************************************)
(*  Helper definitions                                                    *)
(***************************************************************************)
\* The set of all (ballot,value) pairs
BallotValue == Ballot \X Value

\* A permutation of the acceptors
IsPermutation(p) == 
    /\ DOMAIN(p) = Acceptor
    /\ Range(p) = Acceptor
    /\ \A x, y \in Acceptor : p[x] = p[y] => x = y

MCSymmetry == { p \in [Acceptor -> Acceptor] : IsPermutation(p) }

\* Safety of a vote (b,v) at a lower ballot c
SafeAt(b, v) == 
    \A c \in Ballot : 
        (c < b) => 
            \E Q \in Quorum : 
                \A a \in Q : 
                    (<<c, v>> \in votes[a]) \/ (threshold[a] > c)

\* Whether a value v is chosen (a quorum has all voted for v in the same ballot)
Chosen(v) == 
    \E b \in Ballot, Q \in Quorum : 
        \A a \in Q : <<b, v>> \in votes[a]

(***************************************************************************)
(*  Initial state                                                         *)
(***************************************************************************)
Init == 
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

(***************************************************************************)
(*  Actions                                                               *)
(***************************************************************************)

\* 1. Increase promise threshold without voting
Promise(a, b) == 
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > threshold[a]
    /\ UNCHANGED votes
    /\ threshold' = [threshold EXCEPT ![a] = b]

\* 2. Cast a vote for value v in ballot b
Vote(a, b, v) == 
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= threshold[a]                     \* not below current promise
    /\ ~ (<<b, v>> \in votes[a])              \* not already voted in this ballot
    /\ \A aAcc \in Acceptor : 
          \A w \in Value :
                (<<b, w>> \in votes[aAcc]) => w = v   \* at most one value per ballot
    /\ \E Q \in Quorum : 
          \A aAcc \in Q : 
              (<<b, v>> \in votes[aAcc]) \/ (threshold[aAcc] > b)   \* quorum safety witness
    /\ SafeAt(b, v)                         \* vote itself must be safe
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

\* Next is the disjunction of all possible actions of any acceptor
Next == 
    \E a \in Acceptor :
        \/ \E b \in Ballot : Promise(a, b)
        \/ \E b \in Ballot, v \in Value : Vote(a, b, v)

(***************************************************************************)
(*  Specification                                                         *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<votes, threshold>>

(***************************************************************************)
(*  Invariant                                                             *)
(***************************************************************************)

\* Type correctness
TypeCorrect == 
    /\ \A a \in Acceptor : votes[a] \subseteq BallotValue
    /\ \A a \in Acceptor : threshold[a] \in Int

\* Every vote cast is safe at its ballot number
AllVotesSafe == 
    \A a \in Acceptor : 
        \A <<b, v>> \in votes[a] : SafeAt(b, v)

\* At most one value is voted for in any given ballot
OneValuePerBallot == 
    \A b \in Ballot : 
        \A vv1, vv2 \in Value :
            ( (\E aA \in Acceptor : <<b, vv1>> \in votes[aA]) /\ 
              (\E aB \in Acceptor : <<b, vv2>> \in votes[aB]) ) => vv1 = vv2

Inv == TypeCorrect /\ AllVotesSafe /\ OneValuePerBallot

(***************************************************************************)
(*  Safety property (consensus)                                           *)
(***************************************************************************)
ConsensusSpecBar == 
    \A val1, val2 \in Value : (Chosen(val1) /\ Chosen(val2)) => val1 = val2

=============================================================================