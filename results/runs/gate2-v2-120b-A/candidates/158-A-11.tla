---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(*  Constants (to be instantiated in the .cfg file)                        *)
(***************************************************************************)
CONSTANTS
    Acceptor,   \* Set of acceptors
    Value,      \* Set of possible values
    Quorum,     \* Set of quorums, each quorum is a subset of Acceptor
    Ballot      \* Set of ballot numbers (natural numbers, bounded in cfg)

(***************************************************************************)
(*  Types and derived constants                                            *)
(***************************************************************************)
Vote == [b : Ballot, v : Value]

\* Safety assumption: every two quorums overlap
QuorumOverlap == 
    \A q1, q2 \in Quorum : q1 # q2 => q1 \cap q2 # {}

(***************************************************************************)
(*  Variables                                                             *)
(***************************************************************************)
VARIABLES
    votes,      \* [a \in Acceptor |-> SUBSET Vote] – the set of votes each acceptor has cast
    thr         \* [a \in Acceptor |-> Ballot] – promise threshold per acceptor

(***************************************************************************)
(*  Helper definitions                                                    *)
(***************************************************************************)
\* The set of votes for a particular ballot
BallotVotes(b) == { [a, v] \in [Acceptor -> Value] :
                     \E a \in Acceptor : [b, v] \in votes[a] }

\* The (unique, if any) value voted for in ballot b
BallotValue(b) == 
    IF \E v \in Value : \A a \in Acceptor :
           ([b, v] \in votes[a]) \/ (\A v2 \in Value : [b, v2] \notin votes[a])
    THEN CHOOSE v \in Value : \A a \in Acceptor : [b, v] \in votes[a]
    ELSE NULL

\* Quorums that have unanimously voted for value v in ballot b
QuorumVotedFor(b, v) == { q \in Quorum : \A a \in q : [b, v] \in votes[a] }

\* Safety of a value at a ballot number
SafeAt(b, v) ==
    \A c \in Ballot :
        c < b => 
            \E q \in Quorum :
                \A a \in q :
                    ([c, v] \in votes[a]) \/ (thr[a] > c)

\* Whether a value is chosen (i.e., some quorum has all members voting for it)
Chosen(v) == \E b \in Ballot : \E q \in Quorum : \A a \in q : [b, v] \in votes[a]

\* The set of values that have been chosen
ChosenSet == { v \in Value : Chosen(v) }

(***************************************************************************)
(*  Initial state                                                         *)
(***************************************************************************)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thr   = [a \in Acceptor |-> -1]

(***************************************************************************)
(*  Actions                                                               *)
(***************************************************************************)
Promote(a, newThr) ==
    /\ a \in Acceptor
    /\ newThr \in Ballot
    /\ newThr > thr[a]
    /\ thr' = [thr EXCEPT ![a] = newThr]
    /\ UNCHANGED votes

Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= thr[a]                           \* ballot not below current threshold
    /\ \A v2 \in Value : [b, v2] \notin votes[a]   \* acceptor hasn't voted in this ballot
    /\ \A a2 \in Acceptor :
           (\E v2 \in Value : [b, v2] \in votes[a2]) => v2 = v   \* no other acceptor voted for a different value in b
    /\ SafeAt(b, v)                          \* safety condition
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [b, v] }]
    /\ thr'   = [thr EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor : \E newThr \in Ballot : Promote(a, newThr)
    \/ \E a \in Acceptor : \E b \in Ballot : \E v \in Value : Vote(a, b, v)

(***************************************************************************)
(*  Specification                                                         *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<votes, thr>>

(***************************************************************************)
(*  Invariant (combines the three invariants described in the text)       *)
(***************************************************************************)
Inv ==
    /\ \A a \in Acceptor :
          \A p \in votes[a] :
              SafeAt(p.b, p.v)                \* (a) Every vote is safe
    /\ \A b \in Ballot :
          \A v1, v2 \in Value :
            (\E a1 \in Acceptor : [b, v1] \in votes[a1]) /\ 
            (\E a2 \in Acceptor : [b, v2] \in votes[a2]) => v1 = v2   \* (b) At most one value per ballot
    /\ \A a \in Acceptor :
          \A p \in votes[a] :
              p.b \in Ballot /\ p.v \in Value                \* (c) Type correctness

(***************************************************************************)
(*  Safety property required by the configuration                         *)
(***************************************************************************)
ConsensusSpecBar == Cardinality(ChosenSet) <= 1

=============================================================================