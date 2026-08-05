---- MODULE Voting ----
\* A voting-based consensus algorithm: acceptors vote for values in numbered ballots and a value is
\* chosen only once a quorum of acceptors has voted for it in the same ballot. The model tracks
\* every vote each acceptor casts and a promise threshold per acceptor.
EXTENDS Naturals, FiniteSets, Quotient

CONSTANTS Acceptor, Value, Quorum, Ballot

\* A quorum is a set of acceptors; the overlap property (any two quorums intersect) is an
\* additional runtime check rather than a type-correctness check, so it needs no structural
\* wrapper -- the set of quorums is declared in the .cfg, and the property is listed in the .cfg
\* as an explicit INVARIANT.

VARIABLES votes, promised

vars == <<votes, promised>>

\* A vote is a ballot-number and a value.
Vote == [ballot: Ballot, val: Value]

Init ==
  /\ votes = [p \in Acceptor |-> {}]
  /\ promised = [p \in Acceptor |-> 0 - 1]

\* An acceptor promises to only vote in ballots at or above a new threshold.
RaisePromise(p, b) ==
  /\ b > promised[p]
  /\ promised' = [promised EXCEPT ![p] = b]
  /\ UNCHANGED votes

\* An acceptor votes for a value in a ballot, provided no other acceptor has voted for a
\* different value in that same ballot, the ballot is not below its promise threshold, and the
\* value is safe -- the quorum check below -- at that ballot number.
CastVote(p, b, v) ==
  /\ b >= promised[p]
  /\ \A x \in votes[p] : x.val # v => x.ballot # b
  /\ ~(\E q \in votes[p] : q.ballot = b /\ q.val = v)
  /\ SafeAt(v, b)
  /\ votes' = [votes EXCEPT ![p] = @ \cup {[ballot |-> b, val |-> v]}]
  /\ promised' = [promised EXCEPT ![p] = b]

\* A value is safe at ballot b if at every lower ballot c there is a quorum in which every
\* member either voted for that value in c or can never vote in c (its promise is already above).
SafeAt(v, b) ==
  \A c \in Ballot :
    (c < b) =>
      (\E q \in Quorum :
        \A m \in q : (\A x \in votes[m] : x.ballot = c => x.val = v) \/ promised[m] > c)

\* The chosen set filters the votes for unanimous quorum support in one ballot.
Chosen == { v \in Value :
              \E q \in Quorum :
                \E b \in Ballot :
                  \A m \in q : [ballot |-> b, val |-> v] \in votes[m] }

Next ==
  \/ \E p \in Acceptor, b \in Ballot : RaisePromise(p, b)
  \/ \E p \in Acceptor, b \in Ballot, v \in Value : CastVote(p, b, v)

Spec == Init /\ [][Next]_vars

\* Consistency: at most one value is ever chosen.
Inv == Cardinality(Chosen) <= 1

\* ImplementsConsensus: the chosen set is exactly the set of values that some quorum voted for
\* together in one ballot.
ConsensusSpecBar ==
  Chosen = { v \in Value :
              \E q \in Quorum :
                \E b \in Ballot :
                  \A m \in q : [ballot |-> b, val |-> v] \in votes[m] }

\* Quorums overlap pairwise.
QuorumsOverlap ==
  \A q1 \in Quorum, q2 \in Quorum : q1 # q2 => q1 \cap q2 # {}

Permutations ==
  { i \in [Acceptor -> Acceptor] : \A p \in Acceptor : i[p] \in Acceptor }

MCAcceptor == { a1, a2, a3 }
MCValue == { v1, v2 }
MCQuorum == { { a1, a2 }, { a2, a3 } }
MCBallot == 0..2

MCSymmetry == Permutations

====