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

ASSUME Acceptor \subseteq Acceptor
ASSUME Value \subseteq Value
ASSUME Quorum \subseteq Quorum
ASSUME Ballot \subseteq Ballot

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, threshold

Votes == [a : Acceptor, value : Value, ballot : Ballot]

TypeOK ==
    /\ votes \subseteq Votes
    /\ threshold \in [MCAcceptor -> MCBallot \cup {-1}]

Init ==
    /\ votes = {}
    /\ threshold = [a \in MCAcceptor |-> -1]

\* An acceptor may raise its promise threshold so it will not vote below
\* that ballot, without casting a vote.
RaiseThreshold(a, b) ==
    /\ threshold[a] < b
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

\* A quorum vouches for a value at a ballot, so the vote is safe there.
SafeAt(v, b) ==
    /\ \A c \in MCBallot : c < b =>
        \E q \in MCQuorum :
            \A a \in q :
                (Votes \cap { [a |-> a, value |-> v, ballot |-> c] } # {})
                \/ (\E d \in MCBallot : d <= c /\ { [a |-> a, value |-> v, ballot |-> d] } \cap Votes = {})
    /\ \A c \in MCBallot : c < b => \A v2 \in MCValue :
        (\E a \in MCAcceptor : [a |-> a, value |-> v2, ballot |-> c] \in votes) => v2 = v

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
    \/ \E a \in MCAcceptor, b \in MCBallot : RaiseThreshold(a, b)
    \/ \E a \in MCAcceptor, v \in MCValue, b \in MCBallot : CastVote(a, v, b)

Spec == Init /\ [][Next]_<<votes, threshold>>

\* A value is "chosen" once a quorum has voted for it in some ballot.
Chosen(v) == \E q \in MCQuorum : \A a \in q : [a |-> a, value |-> v, ballot |-> 0] \in votes

\* SAFETY: at most one value is ever chosen by a quorum of acceptors.
Inv == Cardinality({ v \in MCValue : Chosen(v) }) <= 1

(* A version of the consensus spec that talks directly about the chosen     *)
(* set, shown here as the property being refined to.                        *)
ConsensusSpecBar == Cardinality({ v \in MCValue : Chosen(v) }) <= 1

(* Acceptors are symmetric participants; any permutation of them leaves the*)
(* system's behavior invariant, so symmetry-reducing permutations are safe. *)
MCSymmetry == { p \in [MCAcceptor -> MCAcceptor] : \A q \in MCQuorum : p[q] \in MCQuorum }

====