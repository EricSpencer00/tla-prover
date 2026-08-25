---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

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
   /\ \A a2_ \in Acceptor : \A vv \in Value :
          (<<b, vv>> \in votes[a2_]) => vv = v   \* at most one value per ballot
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
        \A vv1, vv2 \in Value :
           ( (\E aa1 \in Acceptor : <<b, vv1>> \in votes[aa1]) /\
             (\E aa2 \in Acceptor : <<b, vv2>> \in votes[aa2]) ) => vv1 = vv2
   /\ \A a \in Acceptor :
        \A bv \in votes[a] : Safe(bv[2], bv[1])

(* ---------------------------------------------------------------------- *)
Chosen(v) ==
   \E b \in Ballot :
        \E Q \in Quorum :
            \A a \in Q : <<b, v>> \in votes[a]

ConsensusSpecBar ==
   \A vv1, vv2 \in Value : (Chosen(vv1) /\ Chosen(vv2)) => vv1 = vv2

====