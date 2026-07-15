---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants (instantiated in the .cfg)
-----------------------------------------------------------------*)
CONSTANT Acceptor
CONSTANT Value
CONSTANT Quorum
CONSTANT Ballot

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
AcceptorSet == Acceptor
ValueSet    == Value
QuorumSet   == Quorum
BallotSet   == Ballot

(*-----------------------------------------------------------------
  Types
-----------------------------------------------------------------*)
Vote == [b : BallotSet, v : ValueSet]

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLE votes, prom

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Votes(a) == votes[a]
Prom(a)  == prom[a]

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ votes = [a \in AcceptorSet |-> {}]
    /\ prom  = [a \in AcceptorSet |-> -1]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
(* 1. Increase promise threshold *)
Promise(a, b) ==
    /\ a \in AcceptorSet
    /\ b \in BallotSet
    /\ b > Prom(a)
    /\ prom' = [prom EXCEPT ![a] = b]
    /\ UNCHANGED votes

(* 2. Vote for a value in a ballot *)
VoteAction(a, b, v) ==
    /\ a \in AcceptorSet
    /\ b \in BallotSet
    /\ v \in ValueSet
    /\ b >= Prom(a)                     \* respects current promise
    /\ \A w \in Votes(a) : w.b # b      \* hasn't voted in this ballot
    /\ \A a2 \in AcceptorSet :
          \A w \in Votes(a2) :
            (w.b = b) => (w.v = v)      \* no other vote for a different value in same ballot
    /\ SafeAt(b, v)                     \* safety condition
    /\ votes' = [votes EXCEPT ![a] = @ \cup { [b |-> b, v |-> v] }]
    /\ prom'  = [prom  EXCEPT ![a] = b]

(* 3. Stuttering step to avoid deadlock *)
Stutter ==
    UNCHANGED << votes, prom >>

Next ==
    \/ \E a \in AcceptorSet, b \in BallotSet : Promise(a, b)
    \/ \E a \in AcceptorSet, b \in BallotSet, v \in ValueSet : VoteAction(a, b, v)
    \/ Stutter

(*-----------------------------------------------------------------
  Safety condition: a value v is safe at ballot b
-----------------------------------------------------------------*)
SafeAt(b, v) ==
    \A c \in BallotSet :
        (c < b) =>
            \E Q \in QuorumSet :
                \A a \in Q :
                    (\E w \in Votes(a) : w = [b |-> c, v |-> v])
                    \/ (c < Prom(a))

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<votes, prom>>

(*-----------------------------------------------------------------
  Invariant: every vote is safe at its ballot
-----------------------------------------------------------------*)
Inv ==
    \A a \in AcceptorSet :
        \A w \in Votes(a) :
            SafeAt(w.b, w.v)

(*-----------------------------------------------------------------
  Derived state: the set of chosen values (for the refinement mapping)
-----------------------------------------------------------------*)
Chosen ==
    { v \in ValueSet :
        \E b \in BallotSet :
            \E Q \in QuorumSet :
                \A a \in Q :
                    \E w \in Votes(a) : w = [b |-> b, v |-> v] }

(*-----------------------------------------------------------------
  Consensus specification: at most one value is chosen
-----------------------------------------------------------------*)
ConsensusSpecBar ==
    Cardinality(Chosen) <= 1

====