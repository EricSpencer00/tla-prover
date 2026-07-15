---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANT Acceptor        \* set of acceptor identifiers
CONSTANT Value           \* set of values that may be chosen
CONSTANT Quorum          \* set of quorums, each a subset of Acceptor
CONSTANT Ballot          \* set of ballot numbers (natural numbers)

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Quorums == { q \in Quorum : q # {} }   \* optional non‑empty requirement

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES votes, thr

(*-----------------------------------------------------------------
  Type invariant (helps TLC, not the safety invariant)
-----------------------------------------------------------------*)
TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ thr   \in [Acceptor -> Ballot]

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
VoteSet == UNION { votes[a] : a \in Acceptor }

VoteBallots(v) == { b : <<b,_>> \in v }

BallotOf(v) == { b : <<b,_>> \in v }

QuorumIntersection ==
  \A q1, q2 \in Quorums : q1 \cap q2 # {}

(* Safety definition for a value at a specific ballot *)
SafeAt(v, b) ==
  \A c \in { x \in Ballot : x < b } :
    \E q \in Quorums :
      \A a \in q :
        (<<c, v>> \in votes[a]) \/ (thr[a] > c)

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thr   = [a \in Acceptor |-> -1]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)

(* A single acceptor raises its promise threshold *)
RaiseThresh ==
  \E a \in Acceptor, b \in Ballot :
    /\ b > thr[a]
    /\ thr' = [thr EXCEPT ![a] = b]
    /\ UNCHANGED votes

(* An acceptor casts a vote for value v in ballot b *)
Vote ==
  \E a \in Acceptor, b \in Ballot, v \in Value :
    /\ b >= thr[a]                     \* respects current promise
    /\ ~(\E w \in Value : <<b, w>> \in votes[a])  \* hasn't voted in b yet
    /\ \A a2 \in Acceptor :
         (<<b, v>> \in votes[a2]) \/ ~(\E w \in Value : <<b, w>> \in votes[a2])
       \* no other acceptor has voted for a different value in b
    /\ SafeAt(v, b)                    \* value is safe at this ballot
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
    /\ thr'   = [thr EXCEPT ![a] = b]

(* Either a raise or a vote can occur *)
Next ==
  \/ RaiseThresh
  \/ Vote

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<votes, thr>>

(*-----------------------------------------------------------------
  Invariant required by the task
-----------------------------------------------------------------*)
Inv ==
  /\ TypeOK
  /\ QuorumIntersection
  /\ \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
        (<<b, v1>> \in votes[a1] /\ <<b, v2>> \in votes[a2]) => v1 = v2
  /\ \A a \in Acceptor, <<b, v>> \in votes[a] : SafeAt(v, b)

(*-----------------------------------------------------------------
  Property representing the abstract consensus specification
-----------------------------------------------------------------*)
ConsensusSpecBar == Inv

====