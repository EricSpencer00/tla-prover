---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(* Constants (to be instantiated in the .cfg file)                         *)
(***************************************************************************)
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(***************************************************************************)
(* Derived constant operators (substituted by the .cfg)                     *)
(***************************************************************************)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

(***************************************************************************)
(* State variables                                                          *)
(***************************************************************************)
VARIABLES Votes, Threshold

(***************************************************************************)
(* Types of the variables                                                   *)
(***************************************************************************)
VoteRec == [ballot : Ballot, value : Value]

(***************************************************************************)
(* Initial state                                                            *)
(***************************************************************************)
Init ==
    /\ Votes = [a \in Acceptor |-> {}]               \* each acceptor starts with no votes
    /\ Threshold = [a \in Acceptor |-> -1]           \* -1 means “no promise made”

(***************************************************************************)
(* Safety predicate for a (ballot,value) pair                              *)
(***************************************************************************)
Safe(b, v) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( \E vote \in Votes[a] :
                          vote.ballot = c /\ vote.value = v )
                    \/ (Threshold[a] > c)

(***************************************************************************)
(* Action: increase promise threshold                                      *)
(***************************************************************************)
IncreasePromise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > Threshold[a]
    /\ Threshold' = [Threshold EXCEPT ![a] = b]
    /\ UNCHANGED Votes

(***************************************************************************)
(* Action: cast a vote                                                     *)
(***************************************************************************)
CastVote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= Threshold[a]                                 \* respects current promise
    /\ ~(\E vote \in Votes[a] : vote.ballot = b)         \* not voted in this ballot yet
    /\ \A a2 \in Acceptor :
          \A vote2 \in Votes[a2] :
              (vote2.ballot = b) => (vote2.value = v)   \* no different value already voted
    /\ Safe(b, v)                                        \* value is safe at this ballot
    /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup
                 { [ballot |-> b, value |-> v] } ]
    /\ Threshold' = [Threshold EXCEPT ![a] = b]
    /\ UNCHANGED << >>

(***************************************************************************)
(* Next-state relation                                                     *)
(***************************************************************************)
Next ==
    \/ \E a \in Acceptor, b \in Ballot : IncreasePromise(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

(***************************************************************************)
(* Specification                                                            *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<Votes, Threshold>>

(***************************************************************************)
(* Invariant: type correctness and safety                                   *)
(***************************************************************************)
Inv ==
    /\ Votes \in [Acceptor -> SUBSET VoteRec]
    /\ Threshold \in [Acceptor -> Int]
    /\ \A a \in Acceptor :
          \A vote \in Votes[a] :
              Safe(vote.ballot, vote.value)
    /\ \A b \in Ballot :
          \A v1 \in Value, v2 \in Value :
              ( (\E a1 \in Acceptor :
                     \E vote1 \in Votes[a1] :
                         vote1.ballot = b /\ vote1.value = v1) /\
                (\E a2 \in Acceptor :
                     \E vote2 \in Votes[a2] :
                         vote2.ballot = b /\ vote2.value = v2) )
               => v1 = v2

(***************************************************************************)
(* Property expressing consensus consistency                                *)
(***************************************************************************)
ConsensusSpecBar ==
    \A b1, b2 \in Ballot, v1, v2 \in Value, Q1, Q2 \in Quorum :
        ( (\A a \in Q1 :
               \E vote \in Votes[a] :
                    vote.ballot = b1 /\ vote.value = v1) /\
          (\A a \in Q2 :
               \E vote \in Votes[a] :
                    vote.ballot = b2 /\ vote.value = v2) )
        => v1 = v2

(***************************************************************************)
(* Symmetry: permutations of acceptors (identity permutation provided)    *)
(***************************************************************************)
MCSymmetry ==
    { [a \in Acceptor |-> a] }

=============================================================================