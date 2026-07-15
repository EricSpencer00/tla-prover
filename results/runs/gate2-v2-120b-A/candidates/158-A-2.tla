---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

(* --constants as required by the .cfg file *)
CONSTANTS
    Acceptor,      \* set of acceptor identifiers
    Value,         \* set of possible values
    Quorum,        \* set of quorums, each quorum is a subset of Acceptor
    Ballot         \* set of ballot numbers (naturals)

(* derived constant for readability *)
Quorums == Quorum

(*--------------------------------------------------------------------*)
(* Types *)
Vars == << votes, threshold >>

(* votes[a] is a set of pairs <<b, v>> meaning "acceptor a voted for value v in ballot b" *)
(* threshold[a] is the highest ballot number a has promised to, or -1 initially *)
VARIABLES
    votes,          \* [Acceptor -> SUBSET (Ballot \X Value)]
    threshold       \* [Acceptor -> BallotU]

(* Extend Ballot with -1 to represent "no promise made yet" *)
BallotU == Ballot \cup {-1}

(*--------------------------------------------------------------------*)
(* Initial state *)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

(*--------------------------------------------------------------------*)
(* Helper definitions *)

(* The set of all votes ever cast, regardless of acceptor *)
AllVotes == UNION { votes[a] : a \in Acceptor }

(* A quorum is any element of the constant set Quorums *)
IsQuorum(q) == q \in Quorums

(* Overlap property (assumed true for all quorums) *)
QuorumOverlap ==
    \A q1, q2 \in Quorums : q1 # q2 => q1 \cap q2 # {}

(* Safety of a value at a given ballot *)
SafeAt(v, b) ==
    \A c \in Ballot :
        c < b =>
            \E q \in Quorums :
                \A a \in q :
                    (<<c, v>> \in votes[a]) \/ (threshold[a] > c)

(*--------------------------------------------------------------------*)
(* Actions *)

(* 1. An acceptor raises its promise threshold without voting *)
RaisePromise ==
    \E a \in Acceptor :
        \E b \in Ballot :
            /\ b > threshold[a]
            /\ threshold' = [threshold EXCEPT ![a] = b]
            /\ votes' = votes

(* 2. An acceptor votes for a value in a ballot, subject to the conditions *)
Vote ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= threshold[a]
                /\ ~(\E vv \in Value : <<b, vv>> \in votes[a])   \* a has not voted in b
                /\ \A a2 \in Acceptor :
                       a2 # a => ~ (<<b, v2>> \in votes[a2] /\ v2 # v)   \* no other vote for a different value in same ballot
                /\ \E q \in Quorums :
                       \A a2 \in q :
                           <<b, v>> \in votes[a2] \/ (threshold[a2] > b)   \* quorum safety witness
                /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
                /\ threshold' = [threshold EXCEPT ![a] = b]

(* Next-state relation *)
Next ==
    \/ RaisePromise
    \/ Vote

(*--------------------------------------------------------------------*)
(* Specification *)
Spec == Init /\ [][Next]_<<votes, threshold>>

(*--------------------------------------------------------------------*)
(* Derived definitions for the refinement mapping *)

ChosenValues == { v \in Value :
                    \E b \in Ballot :
                        \E q \in Quorums :
                            \A a \in q : <<b, v>> \in votes[a] }

(*--------------------------------------------------------------------*)
(* Invariant required by the .cfg file *)
Inv ==
    /\ \A a \in Acceptor :
          \A <<b, v>> \in votes[a] :
              /\ b \in Ballot
              /\ v \in Value
              /\ b >= threshold[a]           \* a never votes below its threshold
              /\ SafeAt(v, b)                \* every vote is safe
    /\ \A b \in Ballot :
          \A a1, a2 \in Acceptor :
              (<<b, v1>> \in votes[a1] /\ <<b, v2>> \in votes[a2]) => v1 = v2
    /\ QuorumOverlap

(*--------------------------------------------------------------------*)
(* Property required by the .cfg file, derived from the refinement mapping *)
ConsensusSpecBar ==
    \A v1, v2 \in ChosenValues : v1 = v2

=============================================================================