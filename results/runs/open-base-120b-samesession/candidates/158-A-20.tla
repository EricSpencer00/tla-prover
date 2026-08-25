---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* Substitution operators for the model checker *)
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, promise

(* votes[a] is the set of pairs <<ballot , value>> cast by acceptor a *)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ promise = [a \in Acceptor |-> -1]

(* A value v is safe at ballot b if for every lower ballot c there is a quorum
   in which each member has either already voted for v in c or has promised
   to a higher ballot (> c). *)
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) => 
            \E q \in Quorum :
                \A a \in q :
                    (<<c, v>> \in votes[a]) \/ (promise[a] > c)

OneValuePerBallot ==
    \A b \in Ballot :
        \A v1, v2 \in Value :
            ( (\E a1 \in Acceptor : <<b, v1>> \in votes[a1]) /\ 
              (\E a2 \in Acceptor : <<b, v2>> \in votes[a2]) ) => v1 = v2

AllVotesSafe ==
    \A a \in Acceptor :
        \A bv \in votes[a] :
            Safe(bv[2], bv[1])

TypeInv ==
    /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
    /\ promise \in [Acceptor -> Int]

Inv == TypeInv /\ AllVotesSafe /\ OneValuePerBallot

PromiseIncrease(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > promise[a]
    /\ UNCHANGED votes
    /\ promise' = [promise EXCEPT ![a] = b]

CastVote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= promise[a]
    /\ ~(\E bv \in votes[a] : bv[1] = b)                 \* a has not voted in ballot b yet
    /\ \A a2 \in Acceptor :
          \A bv \in votes[a2] :
               (bv[1] = b) => bv[2] = v                \* no different value in same ballot
    /\ \E q \in Quorum : \A a2 \in q : Safe(v, b)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
    /\ promise' = [promise EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor: \E b \in Ballot: PromiseIncrease(a, b)
    \/ \E a \in Acceptor: \E b \in Ballot: \E v \in Value: CastVote(a, b, v)

Spec == Init /\ [][Next]_<<votes, promise>>

(* A value is considered chosen if some quorum has all its members
   voted for that value in the same ballot. *)
ChosenVals ==
    { v \in Value :
        \E b \in Ballot :
            \E q \in Quorum :
                \A a \in q : <<b, v>> \in votes[a] }

ConsensusSpecBar == \A v1, v2 \in ChosenVals : v1 = v2

(* Symmetry: permutations of acceptors that map each quorum to a quorum *)
MCSymmetry ==
    { p \in [Acceptor -> Acceptor] :
        /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2   \* bijection
        /\ \A q \in Quorum :
              { p[a] : a \in q } \in Quorum }

====