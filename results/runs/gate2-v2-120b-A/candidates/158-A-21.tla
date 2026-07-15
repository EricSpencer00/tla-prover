---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

(*--------------------------------------------------------------------
  Constants (instantiated in the .cfg file)
--------------------------------------------------------------------*)
CONSTANT Acceptor      \* Set of acceptor identifiers
CONSTANT Value         \* Set of values that may be chosen
CONSTANT Quorum        \* Set of quorums, each quorum is a subset of Acceptor
CONSTANT Ballot        \* Set of ballot numbers (natural numbers)

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
Quorums == { q \in Quorum : q # {} }   \* Ensure quorums are non‑empty

(*--------------------------------------------------------------------
  Types
--------------------------------------------------------------------*)
Vote == [bal : Ballot, val : Value]

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES votes, thresh

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
VoteSet( a ) == votes[a]

VotesToBallot(b) == { v \in UNION { VoteSet(a) : a \in Acceptor } :
                       v.bal = b }

QuorumsContaining(a) == { q \in Quorums : a \in q }

\* A value v is safe at ballot b if for every lower ballot c there exists
\* a quorum where each member either has already voted for v at c or
\* cannot vote at c because its threshold is already > c.
SafeAt(v, b) ==
  \A c \in Ballot :
    (c < b) =>
      \E q \in Quorums :
        \A a \in q :
          ( [bal |-> c, val |-> v] \in VoteSet(a) ) \/ (thresh[a] > c)

\* Two quorums must overlap – this is required by the description and
\* can be used as an invariant to guard against mis‑instantiation.
QuorumsOverlap ==
  \A q1, q2 \in Quorums : q1 \cap q2 # {}

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thresh = [a \in Acceptor |-> -1]

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
IncreaseThresh(a, b) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ b > thresh[a]
  /\ thresh' = [thresh EXCEPT ![a] = b]
  /\ UNCHANGED votes

CastVote(a, v, b) ==
  /\ a \in Acceptor
  /\ v \in Value
  /\ b \in Ballot
  /\ b >= thresh[a]
  /\ \A w \in VoteSet(a) : w.bal # b               \* a has not voted in b
  /\ \A w \in VotesToBallot(b) :
        w.val = v                                 \* no other value in this ballot
  /\ SafeAt(v, b)                                 \* safety condition
  /\ votes' = [votes EXCEPT ![a] = VoteSet(a) \cup { [bal |-> b, val |-> v] }]
  /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : IncreaseThresh(a, b)
  \/ \E a \in Acceptor, v \in Value, b \in Ballot : CastVote(a, v, b)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<votes, thresh>>

(*--------------------------------------------------------------------
  Derived concepts for invariants and properties
--------------------------------------------------------------------*)
ChosenValues ==
  { v \in Value :
      \E b \in Ballot, q \in Quorums :
        \A a \in q : [bal |-> b, val |-> v] \in VoteSet(a) }

\* Safety invariant: at most one value is ever chosen
Inv ==
  /\ QuorumsOverlap                         \* sanity check on quorums
  /\ \A b \in Ballot :                      \* at most one value per ballot
        Cardinality({ v \in Value :
            \E a \in Acceptor : [bal |-> b, val |-> v] \in VoteSet(a) }) <= 1
  /\ \A a \in Acceptor, v \in VoteSet(a) :
        SafeAt(v.val, v.bal)                \* every vote is safe
  /\ \A a \in Acceptor : thresh[a] \in Int \cup {-1}
  /\ \A a \in Acceptor, v \in VoteSet(a) :
        v.bal >= thresh[a]                  \* threshold respects votes

(*--------------------------------------------------------------------
  Liveness property (placeholder, not checked in the given cfg)
--------------------------------------------------------------------*)
ConsensusSpecBar == ChosenValues \subseteq Value

====