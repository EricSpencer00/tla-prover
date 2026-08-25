---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* aliases for model‑checking constants *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, threshold

(* ----------------------------------------------------------------------
   Types
   ---------------------------------------------------------------------- *)
Vote == [ballot : Ballot, value : Value]

(* ----------------------------------------------------------------------
   Initialization
   ---------------------------------------------------------------------- *)
Init ==
    /\ votes    = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

(* ----------------------------------------------------------------------
   Assumption: every two quorums intersect
   ---------------------------------------------------------------------- *)
QuorumOverlap ==
    \A q1, q2 \in Quorum : q1 # q2 => q1 \cap q2 # {}

(* ----------------------------------------------------------------------
   Safety predicate for a value at a ballot
   ---------------------------------------------------------------------- *)
Safe(b, v) ==
    \A c \in Ballot :
        (c < b) =>
            \E q \in Quorum :
                \A a \in q :
                    (<<c, v>> \in votes[a]) \/ (threshold[a] > c)

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)
Promise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > threshold[a]
    /\ votes'    = votes
    /\ threshold' = [threshold EXCEPT ![a] = b]

CastVote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= threshold[a]                                   \* not below promise
    /\ ~(\E vv \in votes[a] : vv.ballot = b)                \* not voted in b yet
    /\ (\A a2 \in Acceptor :
            ~(\E vv \in votes[a2] :
                    vv.ballot = b /\ vv.value # v))       \* no other value in same ballot
    /\ Safe(b, v)                                           \* value is safe
    /\ votes'    = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \E a \in Acceptor :
        \/ \E b \in Ballot : Promise(a, b)
        \/ \E b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_<<votes, threshold>>

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)
TypeInv ==
    /\ \A a \in Acceptor :
          votes[a] \subseteq { vv \in Vote : vv.ballot \in Ballot /\ vv.value \in Value }
    /\ \A a \in Acceptor : threshold[a] \in Ballot \cup {-1}

AtMostOneValuePerBallot ==
    /\ \A a1, a2 \in Acceptor :
          \A vv1 \in votes[a1] :
              \A vv2 \in votes[a2] :
                  (vv1.ballot = vv2.ballot) => (vv1.value = vv2.value)

AllVotesSafe ==
    /\ \A a \in Acceptor :
          \A vv \in votes[a] :
              Safe(vv.ballot, vv.value)

Inv == TypeInv /\ AtMostOneValuePerBallot /\ AllVotesSafe

(* ----------------------------------------------------------------------
   Derived notion of a chosen value
   ---------------------------------------------------------------------- *)
ChosenVals ==
    { v \in Value :
        \E b \in Ballot, q \in Quorum :
            \A a \in q : <<b, v>> \in votes[a] }

ConsensusSpecBar ==
    \A v1, v2 \in ChosenVals : v1 = v2

(* ----------------------------------------------------------------------
   Symmetry set (identity permutation is always present)
   ---------------------------------------------------------------------- *)
MCSymmetry ==
    { f \in [Acceptor -> Acceptor] :
        /\ \A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2   \* bijection on a finite set
        /\ \A q \in Quorum : f[ q ] \in Quorum }                \* image of a quorum is a quorum

====