---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

(*-----------------------------------------------------------------
  CONSTANTS (instantiated in the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS Acceptor, Value, Quorum, Ballot

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Acceptors == Acceptor
Values    == Value
Ballots   == Ballot
Quorums   == Quorum

(*-----------------------------------------------------------------
  Types
-----------------------------------------------------------------*)
Vote == [ballot : Ballots, val : Values]

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES votes, threshold

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
VotesOf(a) == votes[a]

(* Is there a quorum that has already voted for value v in ballot b? *)
QuorumVotedFor(v, b) ==
  \E q \in Quorums :
    \A a \in q : [ballot |-> b, val |-> v] \in votes[a]

(* There exists a quorum that can certify that v is safe at ballot b *)
Safe(v, b) ==
  \A c \in Ballots :
    (c < b) =>
      \E q \in Quorums :
        \A a \in q :
          ( [ballot |-> c, val |-> v] \in votes[a] )
          \/ (threshold[a] > c)

(* Quorum overlap property – required but not used directly in actions *)
QuorumOverlap ==
  \A q1, q2 \in Quorums : q1 \cap q2 # {}

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ votes = [a \in Acceptors |-> {}]
  /\ threshold = [a \in Acceptors |-> -1]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
(* An acceptor may raise its promise threshold *)
RaiseThresh(a) ==
  \E n \in Ballots :
    /\ n > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = n]
    /\ UNCHANGED votes

(* An acceptor votes for value v in ballot b, provided all safety
   conditions hold. *)
VoteFor(a) ==
  \E b \in Ballots :
    \E v \in Values :
      /\ b >= threshold[a]
      /\ ~(\E w \in votes[a] : w.ballot = b)               \* not already voted in b
      /\ \A a2 \in Acceptors :
            \A w \in votes[a2] :
               (w.ballot = b) => (w.val = v)               \* at most one value per ballot
      /\ Safe(v, b)                                        \* safety condition
      /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, val |-> v] }]
      /\ threshold' = [threshold EXCEPT ![a] = b]
      /\ UNCHANGED << >>

(* Combined next-step relation *)
Next ==
  \/ \E a \in Acceptors : RaiseThresh(a)
  \/ \E a \in Acceptors : VoteFor(a)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<votes, threshold>>

(*-----------------------------------------------------------------
  Invariant components
-----------------------------------------------------------------*)
Inv == ConsistencyInv

(* At most one value is ever chosen (i.e., appears in a quorum of
   votes for the same ballot). *)
ConsistencyInv ==
  \A b \in Ballots :
    \A v1, v2 \in Values :
      ( ( \E q1 \in Quorums :
            \A a \in q1 : [ballot |-> b, val |-> v1] \in votes[a] )
        /\ ( \E q2 \in Quorums :
            \A a \in q2 : [ballot |-> b, val |-> v2] \in votes[a] ) )
      => v1 = v2

(*-----------------------------------------------------------------
  Liveness (not specified, but we must give a name)
-----------------------------------------------------------------*)
ConsensusSpecBar == TRUE

====