---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

(*---------------------------------------------------------------------*)
(*  Constants (to be instantiated in the .cfg)                         *)
(*---------------------------------------------------------------------*)
CONSTANT Acceptor
CONSTANT Value
CONSTANT Quorum
CONSTANT Ballot

(*---------------------------------------------------------------------*)
(*  Types                                                              *)
(*---------------------------------------------------------------------*)
TypeInvariant == 
    /\ Acceptor /= {}
    /\ Value    /= {}
    /\ Quorum   /= {}
    /\ Ballot   /= {}

(*---------------------------------------------------------------------*)
(*  State variables                                                    *)
(*---------------------------------------------------------------------*)
VARIABLES votes, prom

(* votes[ a ] is the set of votes cast by acceptor a.
   Each vote is a record [b |-> ballot number, v |-> value]. *)
(* prom[ a ] is the current promise threshold of acceptor a. *)

(*---------------------------------------------------------------------*)
(*  Utility definitions                                               *)
(*---------------------------------------------------------------------*)
IsVote(v) == 
    /\ v \in {[b : Ballot |-> b] \cup {[v : Value |-> v]}}
    /\ v.b \in Ballot
    /\ v.v \in Value

BallotLess(b1, b2) == b1 < b2

(*---------------------------------------------------------------------*)
(*  Safety predicate: a value v is safe at ballot b                     *)
(*---------------------------------------------------------------------*)
SafeAt(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E q \in Quorum :
                \A a \in q :
                    ( \E vt \in votes[a] : vt.b = c /\ vt.v = v )
                    \/ ( \A vt \in votes[a] : vt.b # c ) \* a cannot vote in c

(*---------------------------------------------------------------------*)
(*  Initial state                                                     *)
(*---------------------------------------------------------------------*)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ prom  = [a \in Acceptor |-> -1]
    /\ TypeInvariant

(*---------------------------------------------------------------------*)
(*  Actions                                                            *)
(*---------------------------------------------------------------------*)
(* 1. An acceptor raises its promise threshold                        *)
RaisePromise ==
    \E a \in Acceptor :
        \E b \in Ballot :
            /\ b > prom[a]
            /\ prom' = [prom EXCEPT ![a] = b]
            /\ UNCHANGED votes

(* 2. An acceptor casts a vote for value v in ballot b                *)
CastVote ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                LET vt == [b |-> b, v |-> v] IN
                /\ b >= prom[a]                     \* not below current promise
                /\ \A vt2 \in votes[a] : vt2.b # b   \* a has not voted in this ballot
                /\ \A a2 \in Acceptor :
                        (~(\E vt2 \in votes[a2] : vt2.b = b) \/ 
                         \A vt2 \in votes[a2] : vt2.v = v)   \* no other acceptor voted for a different value in b
                /\ SafeAt(v, b)                     \* value is safe at b
                /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {vt}]
                /\ prom'  = [prom  EXCEPT ![a] = b]
                /\ UNCHANGED << >>

(* 3. Stuttering step (helps model checking)                         *)
Stutter ==
    UNCHANGED << votes, prom >>

(*---------------------------------------------------------------------*)
(*  Next-state relation                                                *)
(*---------------------------------------------------------------------*)
Next == 
    \/ RaisePromise
    \/ CastVote
    \/ Stutter

(*---------------------------------------------------------------------*)
(*  Specification formula                                              *)
(*---------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<votes, prom>>

(*---------------------------------------------------------------------*)
(*  Safety invariants                                                  *)
(*---------------------------------------------------------------------*)
(* a) Every vote is safe at its ballot number                         *)
VotesAreSafe ==
    \A a \in Acceptor :
        \A vt \in votes[a] :
            SafeAt(vt.v, vt.b)

(* b) At most one value per ballot across all acceptors                *)
AtMostOneValuePerBallot ==
    \A b \in Ballot :
        \A v1, v2 \in Value :
            ( (\E a1 \in Acceptor : \E vt1 \in votes[a1] : vt1.b = b /\ vt1.v = v1) /\
              (\E a2 \in Acceptor : \E vt2 \in votes[a2] : vt2.b = b /\ vt2.v = v2) )
            => v1 = v2

(* c) Type correctness of votes and thresholds                         *)
TypeOk ==
    /\ \A a \in Acceptor : prom[a] \in (-1) \cup Ballot
    /\ \A a \in Acceptor : votes[a] \subseteq {[b |-> Ballot, v |-> Value]}

(* Combined invariant required by the .cfg                               *)
Inv == VotesAreSafe /\ AtMostOneValuePerBallot /\ TypeOk

(*---------------------------------------------------------------------*)
(*  Derived property: consistency (ConsensusSpecBar)                   *)
(*---------------------------------------------------------------------*)
ChosenValues == { vt.v : \E a \in Acceptor : vt \in votes[a] }

ConsensusSpecBar == Cardinality(ChosenValues) <= 1

=============================================================================