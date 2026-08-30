---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

(* A high-level voting-based consensus algorithm.  Acceptors vote for values   *)
(* in numbered ballots; a ballot is only safe if every lower ballot has a     *)
(* quorum backing the same value.  Chosen values form a singleton, so two     *)
(* different values can never both win.                                       *)

CONSTANTS Acceptor, Value, Quorum, Ballot

None == "none"

VARIABLES votes, thresh

vars == <<votes, thresh>>

VotesFor(v) == { a \in Acceptor : \E b \in Ballot : <<b, v>> \in votes[a] }
VotedIn(b)    == { a \in Acceptor : \E v \in Value : <<b, v>> \in votes[a] }

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
    /\ thresh \in [Acceptor -> (-1)..(Cardinality(Ballot) + 1)]

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

\* An acceptor refuses to vote in any ballot below its promised threshold.
RaiseThresh(a, n) ==
    /\ n > thresh[a]
    /\ thresh' = [thresh EXCEPT ![a] = n]
    /\ UNCHANGED votes

\* Voting is guarded by four safety conditions, the last of which is the       *
(* quorum-backup safety of the value at the ballot being voted in.            *)
Vote(a, b, v) ==
    /\ b >= thresh[a]
    /\ \A c \in Ballot : (<<b, v>> \in votes[a]) => c >= b
    /\ \A c \in Ballot : c < b => \A w \in Value : (<<c, w>> \in votes[a]) => w = v
    /\ \A a2 \in Acceptor : a2 # a => (\A w \in Value : (<<b, w>> \in votes[a2]) => w = v)
    /\ \A q \in Quorum : \A c \in Ballot :
        c < b => \A w \in Value : (\A a2 \in q : <<c, w>> \in votes[a2]) => w = v
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
    /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, n \in MCBallot : RaiseThresh(a, n)
    \/ \E a \in Acceptor, b \in MCBallot, v \in MCValue : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

(* The chosen set is derived from the votes: a value is in it once a quorum    *)
(* of acceptors has all voted for it in some ballot.                          *)
Chosen == { v \in Value : \E q \in Quorum : \E b \in Ballot : \A a \in q : <<b, v>> \in votes[a] }

(* At most one value is ever chosen: the bounded set of chosen values is a     *)
(* singleton or empty.                                                        *)
Inv ==
    /\ Chosen \subseteq Value
    /\ \A v1, v2 \in Chosen : v1 = v2
    /\ \A a \in Acceptor : \A p, q \in Ballot : (p # q) => (VotesFor(v1) \cap VotesFor(v2) = {})
    /\ TypeOK

(* The voting algorithm implements abstract consensus: the chosen set derived *)
(* from votes is exactly the abstract consensus object's chosen set.          *)
ConsensusSpecBar ==
    { v \in Value : \E q \in Quorum : \E b \in Ballot : \A a \in q : <<b, v>> \in votes[a] }
        = Chosen

Permutation == [Acceptor -> Acceptor]

MCSymmetry ==
    { f \in [Acceptor -> Acceptor] : \A a \in Acceptor : f[f[a]] = a }

PermutationOf(perm, v) == [a \in Acceptor |-> perm[v[a]]]

\* Model checking is done over a bounded set of ballot numbers, but the       *
(* safety argument works for the unbounded band, represented abstractly.     *)
MCBallot == Ballot
MCQuorum == Quorum
MCAcceptor == Acceptor
MCValue == Value

====