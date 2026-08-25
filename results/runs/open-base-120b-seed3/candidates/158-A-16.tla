---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* ---------------------------------------------------------------------- *)
(*  Derived finite versions for model checking (substituted in the .cfg)   *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

(* ---------------------------------------------------------------------- *)
(*  Basic assumptions about the constants                                 *)
ASSUME /\ a1 /= a2 /\ a1 /= a3 /\ a2 /= a3
ASSUME /\ v1 /= v2
ASSUME /\ \A Q \in Quorum : Q \subseteq Acceptor /\ Q # {}
ASSUME /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME /\ Ballot \subseteq Nat

(* ---------------------------------------------------------------------- *)
(*  Types                                                                  *)
Vote == [ballot : Ballot, value : Value]

(* ---------------------------------------------------------------------- *)
(*  Variables                                                             *)
VARIABLES votes, thresh

(* ---------------------------------------------------------------------- *)
(*  Initialization                                                         *)
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thresh = [a \in Acceptor |-> -1]

(* ---------------------------------------------------------------------- *)
(*  Safety of a value at a ballot                                           *)
Safe(v, b) ==
  \A c \in Ballot :
    (c < b) => 
      \E Q \in Quorum :
        \A a \in Q :
          ( \E vt \in votes[a] : vt.ballot = c /\ vt.value = v )
          \/ ( thresh[a] > c )

(* ---------------------------------------------------------------------- *)
(*  Definition of a chosen value                                            *)
Chosen(v, b) ==
  \E Q \in Quorum :
    \A a \in Q :
      \E vt \in votes[a] : vt.ballot = b /\ vt.value = v

(* ---------------------------------------------------------------------- *)
(*  Actions                                                                *)
PromiseIncrease ==
  \E a \in Acceptor, b \in Ballot :
    /\ b > thresh[a]
    /\ votes' = votes
    /\ thresh' = [thresh EXCEPT ![a] = b]

Vote ==
  \E a \in Acceptor, v \in Value, b \in Ballot :
    /\ b >= thresh[a]
    /\ ~(\E vt \in votes[a] : vt.ballot = b)                      \* a has not voted in b
    /\ \A a2 \in Acceptor :
         \A vt2 \in votes[a2] :
           vt2.ballot = b => vt2.value = v                        \* no conflicting vote
    /\ Safe(v, b)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ thresh' = [thresh EXCEPT ![a] = b]

Next == 
  \/ PromiseIncrease
  \/ Vote

(* ---------------------------------------------------------------------- *)
(*  Specification                                                          *)
Spec == Init /\ [][Next]_<<votes, thresh>>

(* ---------------------------------------------------------------------- *)
(*  Invariant                                                              *)
Inv ==
  /\ \A a \in Acceptor : votes[a] \subseteq Vote
  /\ \A a \in Acceptor : thresh[a] \in Int
  /\ \A b \in Ballot :
        \A v1, v2 \in Value :
          ( \E a1 \in Acceptor : [ballot |-> b, value |-> v1] \in votes[a1] )
          /\ ( \E a2 \in Acceptor : [ballot |-> b, value |-> v2] \in votes[a2] )
          => v1 = v2
  /\ \A a \in Acceptor :
        \A vt \in votes[a] :
          Safe(vt.value, vt.ballot)

(* ---------------------------------------------------------------------- *)
(*  Consensus safety property                                              *)
ConsensusSpecBar == 
  [] ( \A b1, b2 \in Ballot :
        ( \E v1 \in Value : Chosen(v1, b1) )
        /\ ( \E v2 \in Value : Chosen(v2, b2) )
        => v1 = v2 )

(* ---------------------------------------------------------------------- *)
(*  Symmetry set (set of permutations of acceptors)                        *)
MCSymmetry == 
  { p \in [Acceptor -> Acceptor] :
        /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2   \* injective
        /\ \A a \in Acceptor : p[a] \in Acceptor }           \* onto follows from finite domain

====