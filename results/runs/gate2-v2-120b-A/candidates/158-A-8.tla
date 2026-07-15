---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

VARIABLES votes, thresh

(* ------------------------------------------------------------------------- *)
(* Constants (instantiated in the .cfg)                                      *)
(*   a1 - an arbitrary acceptor (used only by the .cfg)                      *)
(*   Acceptor - the finite set of acceptor identifiers                        *)
(*   Value - the finite set of values that can be chosen                     *)
(*   Quorum - a finite set of subsets of Acceptor, each a quorum              *)
(*   Ballot - the finite set of ballot numbers (natural numbers)            *)
(* ------------------------------------------------------------------------- *)

(* Type of a vote *)
Vote == [ballot : Ballot, val : Value]

(* ------------------------------------------------------------------------- *)
(* Initial state                                                            *)
(* ------------------------------------------------------------------------- *)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

(* ------------------------------------------------------------------------- *)
(* Helper definitions                                                       *)
(* ------------------------------------------------------------------------- *)

(* An acceptor a has already voted in ballot b *)
VotedIn(a, b) == \E v \in votes[a] : v.ballot = b

(* The value (if any) that acceptor a has voted for in ballot b *)
VotedValue(a, b) == 
    LET S == { v.val : v \in votes[a] /\ v.ballot = b } IN
    IF S = {} THEN NULL ELSE CHOOSE v \in S : TRUE

(* A quorum q has unanimously voted for value v in ballot b *)
QuorumVotes(q, b, v) ==
    \A a \in q : \E vt \in votes[a] : vt.ballot = b /\ vt.val = v

(* Safe predicate for a value at a given ballot *)
SafeAt(v, b) ==
    \A c \in Ballot : 
        (c < b) => 
            \E q \in Quorum : 
                \A a \in q :
                    ( \E vt \in votes[a] : vt.ballot = c /\ vt.val = v )
                    \/ ~\E vt \in votes[a] : vt.ballot = c

(* ------------------------------------------------------------------------- *)
(* Actions                                                                  *)
(* ------------------------------------------------------------------------- *)

(* An acceptor raises its promise threshold without voting *)
RaisePromise ==
    \E a \in Acceptor :
        \E newThresh \in Ballot :
            /\ newThresh > thresh[a]
            /\ thresh' = [thresh EXCEPT ![a] = newThresh]
            /\ UNCHANGED votes

(* An acceptor votes for a value in a ballot, respecting all constraints *)
VoteAction ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= thresh[a] + 1          \* (b not below current threshold)
                /\ ~VotedIn(a, b)               \* a has not voted in b yet
                /\ \A a2 \in Acceptor :
                       ( VotedIn(a2, b) => VotedValue(a2, b) = v )
                /\ \E q \in Quorum : QuorumVotes(q, b, v)
                /\ votes' = [votes EXCEPT ![a] = 
                               votes[a] \cup { [ballot |-> b, val |-> v] }]
                /\ thresh' = [thresh EXCEPT ![a] = b]
                /\ UNCHANGED << >>

(* ------------------------------------------------------------------------- *)
(* Next-state relation                                                       *)
(* ------------------------------------------------------------------------- *)
Next ==
    \/ RaisePromise
    \/ VoteAction

(* ------------------------------------------------------------------------- *)
(* Specification                                                            *)
(* ------------------------------------------------------------------------- *)
Spec ==
    Init /\ [][Next]_<<votes, thresh>>

(* ------------------------------------------------------------------------- *)
(* Invariant: every vote that has been cast is safe at its ballot number      *)
(* ------------------------------------------------------------------------- *)
Inv ==
    \A a \in Acceptor :
        \A vt \in votes[a] :
            SafeAt(vt.val, vt.ballot)

(* ------------------------------------------------------------------------- *)
(* Derived safety property: at most one value can ever be chosen            *)
(* ------------------------------------------------------------------------- *)
ConsensusSpecBar ==
    \A b \in Ballot :
        \A v1, v2 \in Value :
            ( (\E q1 \in Quorum : QuorumVotes(q1, b, v1)) /\ 
              (\E q2 \in Quorum : QuorumVotes(q2, b, v2)) ) => v1 = v2

====