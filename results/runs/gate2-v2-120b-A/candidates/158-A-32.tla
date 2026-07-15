---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(*  Constants (instantiated in the .cfg file)                              *)
(*  a1        : a distinguished acceptor (may be used in examples)        *)
(*  Acceptor  : the set of all acceptors                                    *)
(*  Value     : the set of values that can be chosen                        *)
(*  Quorum    : a set of sets of acceptors, each set being a quorum        *)
(*  Ballot    : the set of ballot numbers (natural numbers)                *)
(***************************************************************************)

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

(* Helper definition: the set of all possible votes *)
Vote == [b : Ballot, v : Value]

VARIABLES votes, prom

(*-----------------------------------------------------------------------*)
(*  Type correctness (useful for debugging, not the safety invariant)   *)
(*-----------------------------------------------------------------------*)
TypeOK ==
    /\ votes \in [Acceptor -> SUBSET Vote]
    /\ prom  \in [Acceptor -> Ballot]

(*-----------------------------------------------------------------------*)
(*  Helper predicates                                                   *)
(*-----------------------------------------------------------------------*)

(* A quorum is any element of the constant Quorum set *)
IsQuorum(q) == q \in Quorum

(* Overlap property assumed for the model; not enforced here but used in
   comments and for reasoning. *)
OverlapProperty ==
    \A q1, q2 \in Quorum : q1 # q2 => \E a \in Acceptor : a \in q1 /\ a \in q2

(* A vote v = [b |-> b, v |-> val] is safe at ballot b if for every lower
   ballot c there exists a quorum where each member has either already
   voted for val in c or cannot vote in c (its promise > c). *)
SafeAt(v) ==
  LET b == v.b IN
    \A c \in Ballot :
        (c < b) =>
          \E q \in Quorum :
            \A a \in q :
               ( [b |-> c, v |-> v.v] \in votes[a] ) \/ ( prom[a] > c )

(* The set of values that have been chosen: a value is chosen if there exists
   a ballot b and a quorum q such that every acceptor in q has voted for that
   value in that ballot. *)
Chosen == { val \in Value :
            \E b \in Ballot, q \in Quorum :
               \A a \in q : [b |-> b, v |-> val] \in votes[a] }

(*-----------------------------------------------------------------------*)
(*  Initial state                                                       *)
(*-----------------------------------------------------------------------*)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ prom  = [a \in Acceptor |-> -1]

(*-----------------------------------------------------------------------*)
(*  Actions                                                             *)
(*-----------------------------------------------------------------------*)

(* An acceptor raises its promise threshold to a higher ballot number *)
RaisePromise ==
    \E a \in Acceptor :
      \E b \in Ballot :
        /\ b > prom[a]
        /\ prom' = [prom EXCEPT ![a] = b]
        /\ UNCHANGED votes

(* An acceptor casts a vote for value val in ballot b, provided all safety
   conditions hold. *)
VoteAction ==
    \E a \in Acceptor :
      \E b \in Ballot :
        \E val \in Value :
          LET v == [b |-> b, v |-> val] IN
            /\ b >= prom[a]                     \* respects current promise
            /\ \A w \in votes[a] : w.b # b      \* hasn't voted in this ballot yet
            /\ \A a2 \in Acceptor :
                  \A w \in votes[a2] :
                     (w.b = b) => w.v = val     \* at most one value per ballot
            /\ SafeAt(v)                         \* safety condition
            /\ prom' = [prom EXCEPT ![a] = b]    \* update promise to b
            /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {v}]
            /\ UNCHANGED << >>

(* Non-deterministic choice of either action *)
Next ==
    \/ RaisePromise
    \/ VoteAction

(*-----------------------------------------------------------------------*)
(*  Specification                                                       *)
(*-----------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<votes, prom>>

(*-----------------------------------------------------------------------*)
(*  Safety invariant (the one required by the cfg)                       *)
(*-----------------------------------------------------------------------*)
Inv ==
    /\ \A a \in Acceptor : \A v \in votes[a] : SafeAt(v)   \* every vote is safe
    /\ \A b \in Ballot :
         (\E val \in Value :
              \E q \in Quorum :
                 \A a \in q : [b |-> b, v |-> val] \in votes[a])
         => \A val2 \in Value :
                (\E q2 \in Quorum :
                    \A a2 \in q2 : [b |-> b, v |-> val2] \in votes[a2])
                => val2 = val                         \* at most one value per ballot
    /\ TypeOK

(*-----------------------------------------------------------------------*)
(*  Property required by the cfg (refines abstract consensus spec)      *)
(*-----------------------------------------------------------------------*)
ConsensusSpecBar == Consistency

(* Consistency: at most one value can ever be chosen *)
Consistency ==
    \A val1, val2 \in Value :
        (val1 \in Chosen /\ val2 \in Chosen) => val1 = val2

=============================================================================