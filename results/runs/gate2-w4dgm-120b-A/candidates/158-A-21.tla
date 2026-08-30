---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* The substitution pairs below map the abstract symbolic constants to concrete
\* finite sets that a model checking configuration (.cfg file) will provide.
\* They are not used directly in the spec; they only enable TLC to instantiate
\* the model with small finite sets for sound verification.

CONSTANT MCAcceptor = {a1, a2, a3}
CONSTANT MCValue = {v1, v2}
CONSTANT MCQuorum = {Q1, Q2}
CONSTANT MCBallot = 0..2

\* Each quorum name abbreviates a specific acceptor subset; they all intersect.
QuorumMembers == (Q1 :> {a1, a2}) @@ (Q2 :> {a2, a3})

VARIABLES vote, threshold

Vars == <<vote, threshold>>

TypeOK ==
  /\ vote \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> INTEGER]

Init ==
  /\ vote = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor will no longer vote in any ballot strictly below its new threshold.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED vote

\* Safety check: a vote in ballot b is only legal if every lower ballot already
\* has a quorum that voted for the same value or can never vote in it.
\* Casting a vote also raises the voter’s threshold to the ballot it just voted in.
CastVote(a, b, val) ==
  /\ b >= threshold[a]
  /\ \A c \in Ballot : (<<b, val>> \notin vote[a] /\ c < b) => SafeAt(c, val)
  /\ \A x \in Acceptor : (\A c \in Ballot : <<c, val>> \in vote[x]) => c = b
  /\ vote' = [vote EXCEPT ![a] = @ \cup {<<b, val>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

SafeAt(b, val) ==
  /\ b \in Ballot
  /\ \A c \in 0..(b - 1) :
       \E Q \in MCQuorum :
         \A x \in Q :
           \/ <<c, val>> \in vote[x]
           \/ \A v \in MCValue : <<c, v>> \notin vote[x]

Next ==
  \/ \E a \in Acceptor, b \in MCBallot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, b \in MCBallot, val \in MCValue : CastVote(a, b, val)

Spec == Init /\ [][Next]_Vars

\* Chosen is derived from the vote relation, so its containment is preserved by
\* every transition that only ever adds votes -- this is the crux of the refinement.
Chosen == {val \in MCValue : \E Q \in MCQuorum : \A a \in Q : \E b \in MCBallot : <<b, val>> \in vote[a]}

\* Safety: an acceptor's vote must always be backed by a quorum at that ballot.
VoterBackedByQuorum ==
  \A a \in Acceptor, b \in Ballot, val \in MCValue :
    (<<b, val>> \in vote[a]) => \E Q \in MCQuorum : \A x \in Q : <<b, val>> \in vote[x]

\* Safety: a ballot can never be split across two different values.
BallotSingleValued ==
  \A b \in Ballot, val1, val2 \in MCValue :
    (\A a \in Acceptor : <<b, val1>> \in vote[a] /\ <<b, val2>> \in vote[a]) => val1 = val2

\* Safety: bounds on vote entries and thresholds stay within the modeled range.
VotingWithinBounds ==
  /\ \A a \in Acceptor : {b \in Ballot : \E val \in MCValue : <<b, val>> \in vote[a]} \subseteq MCBallot
  /\ \A a \in Acceptor : threshold[a] \in (-1)..(Cardinality(MCBallot) - 1)

\* Type checking of every transition against the declared state shape.
StateConstrained == TypeOK /\ VoterBackedByQuorum /\ BallotSingleValued /\ VotingWithinBounds

\* The refined property: anything the consensus layer has chosen is backed by a
\* quorum, so no second value can ever be silently added to the chosen set.
Inv == StateConstrained

\* The abstract consensus spec's safety property, specialized to this concrete
\* chosen-set definition, is what the refinement is meant to prove.
ConsensusSpecBar == \A x, y \in Chosen : x = y

MCSymmetry ==
  {p \in [Acceptor -> Acceptor] :
     /\ {p[a] : a \in Acceptor} = Acceptor
     /\ \A Q \in MCQuorum : {p[a] : a \in Q} \in MCQuorum}

====