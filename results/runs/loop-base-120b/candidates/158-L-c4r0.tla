---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* MC* operators substituted for the corresponding constants *)
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

(* Record representing a single vote *)
Vote == [b : Ballot, v : Value]

VARIABLES votes, thresh

(* ------------------------------------------------------------------------ *)
(* Initial state                                                            *)
(* ------------------------------------------------------------------------ *)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

(* ------------------------------------------------------------------------ *)
(* Helper predicates                                                       *)
(* ------------------------------------------------------------------------ *)
AlreadyVotedIn(a, b) ==
    \E w \in votes[a] : w.b = b

NoConflictingVote(b, v) ==
    \A a2 \in Acceptor: \A w \in votes[a2] :
        (w.b = b) => (w.v = v)

(* Safety of a vote at ballot b for value v *)
Safe(b, v) ==
    \A c \in Ballot :
        (c < b) => 
            \E Q \in Quorum :
                \A a \in Q :
                    (\E w \in votes[a] : w.b = c /\ w.v = v) \/ (thresh[a] > c)

(* ------------------------------------------------------------------------ *)
(* Actions                                                                  *)
(* ------------------------------------------------------------------------ *)
Promote(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > thresh[a]                \* raise the promise threshold
    /\ UNCHANGED votes
    /\ thresh' = [thresh EXCEPT ![a] = b]

VoteAction(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= thresh[a]               \* not below current promise
    /\ ~AlreadyVotedIn(a, b)        \* hasn't voted in this ballot yet
    /\ NoConflictingVote(b, v)      \* no different value already voted in b
    /\ Safe(b, v)                   \* safety condition holds
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [b |-> b, v |-> v] }]
    /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor: \E b \in Ballot: Promote(a, b)
    \/ \E a \in Acceptor: \E b \in Ballot: \E v \in Value: VoteAction(a, b, v)

(* ------------------------------------------------------------------------ *)
(* Specification                                                            *)
(* ------------------------------------------------------------------------ *)
Spec == Init /\ [][Next]_<<votes, thresh>>

(* ------------------------------------------------------------------------ *)
(* Invariant(s)                                                             *)
(* ------------------------------------------------------------------------ *)
TypeInv ==
    /\ votes \in [Acceptor -> SUBSET Vote]
    /\ \A a \in Acceptor: \A w \in votes[a] :
          /\ w.b \in Ballot
          /\ w.v \in Value
    /\ thresh \in [Acceptor -> Int]
    /\ \A a \in Acceptor: thresh[a] = -1 \/ thresh[a] \in Ballot

OneValuePerBallot ==
    \A b \in Ballot :
        LET vals == { v \in Value :
                        \E a \in Acceptor: \E w \in votes[a] :
                            w.b = b /\ w.v = v }
        IN Cardinality(vals) <= 1

AllVotesSafe ==
    \A a \in Acceptor: \A w \in votes[a] : Safe(w.b, w.v)

Inv == TypeInv /\ OneValuePerBallot /\ AllVotesSafe

(* ------------------------------------------------------------------------ *)
(* Consistency property                                                     *)
(* ------------------------------------------------------------------------ *)
ConsensusSpecBar ==
    \A b1, b2 \in Ballot, v1, v2 \in Value :
        ( \E Q1 \in Quorum :
            \A a \in Q1 :
                \E w \in votes[a] : w.b = b1 /\ w.v = v1 )
        /\ ( \E Q2 \in Quorum :
            \A a \in Q2 :
                \E w \in votes[a] : w.b = b2 /\ w.v = v2 )
        => v1 = v2

(* ------------------------------------------------------------------------ *)
(* Symmetry set (all permutations of Acceptor)                              *)
(* ------------------------------------------------------------------------ *)
MCSymmetry ==
    { f \in [Acceptor -> Acceptor] :
        /\ \A a \in Acceptor: f[a] \in Acceptor
        /\ \A a1, a2 \in Acceptor: f[a1] = f[a2] => a1 = a2 }

====