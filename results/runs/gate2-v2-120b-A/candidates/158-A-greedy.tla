---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

(*-----------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS
    a1,          \* a distinguished acceptor (not used directly, but required)
    Acceptor,    \* the set of all acceptors
    Value,       \* the set of all values that may be chosen
    Quorum,      \* the set of all quorum subsets of Acceptor
    Ballot       \* the set of ballot numbers (natural numbers, bounded in cfg)

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Quorums == { q \in SUBSET Acceptor : q \in Quorum }

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES
    votes,       \* [a \in Acceptor -> SUBSET { <<b, v>> : b \in Ballot, v \in Value }]
    threshold    \* [a \in Acceptor -> Ballot]  (the promise threshold)

(*-----------------------------------------------------------------
  Type correctness (useful for debugging, not the main invariant)
-----------------------------------------------------------------*)
TypeOK ==
    /\ votes \in [Acceptor -> SUBSET { <<b, v>> : b \in Ballot, v \in Value }]
    /\ threshold \in [Acceptor -> Ballot]

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
VotePair == <<b, v>> \* a pair representing a vote

VoteOf(a) == votes[a]          \* the set of votes cast by acceptor a

HasVotedInBallot(a, b) == \E v \in Value : <<b, v>> \in votes[a]

VoteValue(a, b) == 
    CHOOSE v \in Value : <<b, v>> \in votes[a]

(* A quorum q demonstrates that value v is safe at ballot b *)
SafeAt(v, b) ==
    \A c \in Ballot :
        (c < b) => 
            \E q \in Quorums :
                \A a \in q :
                    (<<c, v>> \in votes[a]) \/ (threshold[a] > c)

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
IncreaseThreshold ==
    \E a \in Acceptor :
        \E newThr \in Ballot :
            /\ newThr > threshold[a]
            /\ threshold' = [threshold EXCEPT ![a] = newThr]
            /\ UNCHANGED votes

CastVote ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= threshold[a]
                /\ ~HasVotedInBallot(a, b)
                /\ \A a2 \in Acceptor :
                       (HasVotedInBallot(a2, b) => VoteValue(a2, b) = v)
                /\ SafeAt(v, b)
                /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
                /\ threshold' = [threshold EXCEPT ![a] = b]
                /\ UNCHANGED << >>

Next == 
    \/ IncreaseThreshold
    \/ CastVote

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<votes, threshold>>

(*-----------------------------------------------------------------
  Derived notion of a chosen value
-----------------------------------------------------------------*)
ChosenValues ==
    { v \in Value :
        \E b \in Ballot :
            \E q \in Quorums :
                \A a \in q : <<b, v>> \in votes[a] }

(*-----------------------------------------------------------------
  Invariant required by the .cfg file
-----------------------------------------------------------------*)
Inv ==
    /\ TypeOK
    /\ \A b \in Ballot :
          \A a1, a2 \in Acceptor :
              (<<b, v1>> \in votes[a1] /\ <<b, v2>> \in votes[a2]) => v1 = v2
    /\ \A a \in Acceptor :
          \A <<b, v>> \in votes[a] : SafeAt(v, b)

(*-----------------------------------------------------------------
  Property required by the .cfg file (consensus specification)
-----------------------------------------------------------------*)
ConsensusSpecBar == 
    \A v1, v2 \in ChosenValues : v1 = v2

====