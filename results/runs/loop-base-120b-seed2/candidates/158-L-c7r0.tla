---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* aliases used by the model checker *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, thresh

(* ---------------------------------------------------------------------- *)
Init ==
   /\ votes = [a \in Acceptor |-> {}]
   /\ thresh = [a \in Acceptor |-> -1]

(* ---------------------------------------------------------------------- *)
Safe(v, b) ==
   \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    (<<c, v>> \in votes[a]) \/ (c < thresh[a])

(* ---------------------------------------------------------------------- *)
Promise(a, b) ==
   /\ a \in Acceptor
   /\ b \in Ballot
   /\ b > thresh[a]                     \* raise the promise threshold
   /\ thresh' = [thresh EXCEPT ![a] = b]
   /\ UNCHANGED votes

Vote(a, b, v) ==
   /\ a \in Acceptor
   /\ b \in Ballot
   /\ v \in Value
   /\ b >= thresh[a]                    \* cannot vote below current promise
   /\ ~\E vv \in Value : <<b, vv>> \in votes[a]   \* not already voted in b
   /\ \A a2 \in Acceptor : \A vv \in Value :
          (<<b, vv>> \in votes[a2]) => vv = v   \* at most one value per ballot
   /\ Safe(v, b)                        \* value is safe at this ballot
   /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
   /\ thresh' = [thresh EXCEPT ![a] = b]

(* ---------------------------------------------------------------------- *)
Next ==
   \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
   \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_<<votes, thresh>>

(* ---------------------------------------------------------------------- *)
Inv ==
   /\ \A a \in Acceptor : thresh[a] >= -1
   /\ \A a \in Acceptor : votes[a] \subseteq Ballot \X Value
   /\ \A b \in Ballot :
        \A v1, v2 \in Value :
           ( (\E a1 \in Acceptor : <<b, v1>> \in votes[a1]) /\ 
             (\E a2 \in Acceptor : <<b, v2>> \in votes[a2]) ) => v1 = v2
   /\ \A a \in Acceptor, <<b, v>> \in votes[a] : Safe(v, b)

(* ---------------------------------------------------------------------- *)
Chosen(v) ==
   \E b \in Ballot :
        \E Q \in Quorum :
            \A a \in Q : <<b, v>> \in votes[a]

ConsensusSpecBar ==
   \A v1, v2 \in Value : (Chosen(v1) /\ Chosen(v2)) => v1 = v2

(* ---------------------------------------------------------------------- *)
MCSymmetry == { [a \in Acceptor |-> a] }   \* identity permutation

(* ---------------------------------------------------------------------- *)
ASSUME \A Q1, Q2 \in Quorum :
          Q1 # {} /\ Q2 # {} => Q1 \cap Q2 # {}

=============================================================================