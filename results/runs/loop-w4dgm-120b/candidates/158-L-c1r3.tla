---- MODULE Voting ----
EXTENDS Integers, FiniteSets

(* A voting-based consensus algorithm abstracted from Paxos.  Acceptors      *)
(* cast votes for values in numbered ballots, and a ballot's vote is       *)
(* accepted only if it is safe: no other value has already been voted for *)
(* that ballot, and a quorum of acceptors can vouch for it at that ballot.*)
(* SAFETY PROPERTY: the set of chosen values is always a subset of size   *)
(* at most one -- two different values can never both be chosen.           *)

(* Constants are declared as symbols here; a separate .cfg file binds them *)
(* to concrete finite sets for model checking.  Operators MCAcceptor,     *)
(* MCValue, MCQuorum, and MCBallot give the bounded/finite versions the     *)
(* model checker should use for the corresponding abstract sets.           *)

CONSTANTS Acceptor, Value, Quorum, Ballot

AssumeAcceptor == Acceptor
AssumeValue == Value
AssumeQuorum == Quorum
AssumeBallot == Ballot

VARIABLES votes, threshold

Votes == [a : Acceptor, value : Value, ballot : Ballot]

TypeOK ==
    /\ votes \subseteq Votes
    /\ threshold \in [AssumeAcceptor -> AssumeBallot \cup {-1}]

Init ==
    /\ votes = {}
    /\ threshold = [a \in AssumeAcceptor |-> -1]

\* An acceptor may raise its promise threshold so it will not vote below
\* that ballot, without casting a vote.
RaiseThreshold(a, b) ==
    /\ threshold[a] < b
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

\* A quorum vouches for a value at a ballot, so the vote is safe there.
SafeAt(v, b) ==
    /\ \A c \in AssumeBallot : c < b =>
        \E q \in AssumeQuorum :
            \A a \in q :
                (Votes \cap { [a |-> a, value |-> v, ballot |-> c] } # {})
                \/ (\E d \in AssumeBallot : d <= c /\ { [a |-> a, value |-> v, ballot |-> d] } \cap votes = {})
    /\ \A c \in AssumeBallot : c < b => \A v2 \in AssumeValue :
        (\E a \in AssumeAcceptor : [a |-> a, value |-> v2, ballot |-> c] \in votes) => v2 = v

\* Casting a vote is subject to the ballot threshold, quorum safety, and the
\* fact that no other acceptor has already voted for a different value in
\* that same ballot.
CastVote(a, v, b) ==
    /\ threshold[a] < b
    /\ \A x \in votes : ~(x.a = a /\ x.ballot = b)
    /\ \A x \in votes : x.ballot = b => x.value = v
    /\ SafeAt(v, b)
    /\ votes' = votes \cup { [a |-> a, value |-> v, ballot |-> b] }
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in AssumeAcceptor, b \in AssumeBallot : RaiseThreshold(a, b)
    \/ \E a \in AssumeAcceptor, v \in AssumeValue, b \in AssumeBallot : CastVote(a, v, b)

Spec == Init /\ [][Next]_<<votes, threshold>>

\* A value is "chosen" once a quorum has voted for it in some ballot.
Chosen(v) == \E q \in AssumeQuorum : \A a \in q : [a |-> a, value |-> v, ballot |-> 0] \in votes

\* SAFETY: at most one value is ever chosen by a quorum of acceptors.
Inv == Cardinality({ v \in AssumeValue : Chosen(v) }) <= 1

(* A version of the consensus spec that talks directly about the chosen     *)
(* set, shown here as the property being refined to.                        *)
ConsensusSpecBar == Cardinality({ v \in AssumeValue : Chosen(v) }) <= 1

(* Acceptors are symmetric participants; any permutation of them leaves the*)
(* system's behavior invariant, so symmetry-reducing permutations are safe. *)
MCSymmetry == { p \in [AssumeAcceptor -> AssumeAcceptor] : \A q \in AssumeQuorum : p[q] \in AssumeQuorum }

====