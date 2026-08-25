---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(***************************************************************************)
(*   Substitution operators for the model checker configuration           *)
(***************************************************************************)

MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

(***************************************************************************)
(*   State variables                                                     *)
(***************************************************************************)

VARIABLES votes, prom   \* votes[a] \in SUBSET {[ballot: Ballot, value: Value]};
                      \* prom[a]  \in Int (minimum ballot number the acceptor will
                      \*          consider; initial value -1)

(***************************************************************************)
(*   Helper definitions                                                  *)
(***************************************************************************)

\* The set of all possible votes (pairs of ballot and value)
VoteRec == [ballot : Ballot, value : Value]

\* A quorum must intersect any other quorum (assumed by the model)
QuorumOverlap == 
   \A q1 \in Quorum : 
     \A q2 \in Quorum : 
        q1 # q2 => q1 \cap q2 # {}

\* Safety of a value at a given ballot
Safe(v, b) ==
   \A c \in Ballot :
      (c < b) => 
        \E q \in Quorum :
           \A a \in q :
              ( [ballot |-> c, value |-> v] \in votes[a] ) \/ (prom[a] > c)

\* Whether a value v has been “chosen” (i.e., a quorum has all members
\* voting for it in the same ballot)
ChosenVals == 
   { v \in Value :
        \E b \in Ballot :
          \E q \in Quorum :
            \A a \in q :
               \E vt \in votes[a] :
                  /\ vt.ballot = b
                  /\ vt.value = v }

(***************************************************************************)
(*   Initialization                                                      *)
(***************************************************************************)

Init ==
   /\ votes = [a \in Acceptor |-> {}]
   /\ prom  = [a \in Acceptor |-> -1]

(***************************************************************************)
(*   Actions                                                             *)
(***************************************************************************)

\* An acceptor raises its promise threshold
Promise ==
   \E a \in Acceptor :
     \E b \in Ballot :
        /\ b > prom[a]                     \* raise to a higher ballot
        /\ UNCHANGED votes
        /\ prom' = [prom EXCEPT ![a] = b]

\* An acceptor votes for a value in a ballot
Vote ==
   \E a \in Acceptor :
     \E b \in Ballot :
       \E v \in Value :
          /\ b >= prom[a]                                 \* not below promise
          /\ \A vt \in votes[a] : vt.ballot # b          \* hasn't voted in b yet
          /\ \A a2 \in Acceptor :
                \A vt2 \in votes[a2] :
                   (vt2.ballot = b) => vt2.value = v   \* at most one value per ballot
          /\ Safe(v, b)                                   \* value is safe
          /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
          /\ prom'  = [prom  EXCEPT ![a] = b]

Next == 
   \/ Promise
   \/ Vote

(***************************************************************************)
(*   Specification                                                       *)
(***************************************************************************)

Spec == Init /\ [][Next]_<<votes, prom>>

(***************************************************************************)
(*   Invariant                                                           *)
(***************************************************************************)

Inv ==
   /\ \A a \in Acceptor : \A vt \in votes[a] : vt \in VoteRec
   /\ \A b \in Ballot :
        \A v1, v2 \in Value :
          ( (\E a1 \in Acceptor : \E vt1 \in votes[a1] : vt1.ballot = b /\ vt1.value = v1) /\
            (\E a2 \in Acceptor : \E vt2 \in votes[a2] : vt2.ballot = b /\ vt2.value = v2) )
          => v1 = v2
   /\ \A a \in Acceptor : \A vt \in votes[a] : Safe(vt.value, vt.ballot)

(***************************************************************************)
(*   Safety property (consensus)                                         *)
(***************************************************************************)

ConsensusSpecBar ==
   \A v1, v2 \in Value :
        (v1 \in ChosenVals /\ v2 \in ChosenVals) => v1 = v2

(***************************************************************************)
(*   Symmetry set (permutations of acceptors)                            *)
(***************************************************************************)

MCSymmetry ==
   { p \in [Acceptor -> Acceptor] :
        /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2   \* injective
        /\ \A a \in Acceptor : p[a] \in Acceptor }           \* total bijection

============================================================================