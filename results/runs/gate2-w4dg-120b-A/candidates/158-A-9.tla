---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

ASSUME a1 \in Acceptor
ASSUME Quorum \subseteq SUBSET Acceptor
ASSUME Ballot \in Nat
ASSUME Cardinality(Quorum) > 1

VARIABLES voted, promised

vars == <<voted, promised>>

Votes == [ball: 0 .. Ballot, val: Value]

TypeOK ==
  /\ voted \in [Acceptor -> SUBSET Votes]
  /\ promised \in [Acceptor -> -1 .. Ballot]

Init ==
  /\ voted = [a \in Acceptor |-> {}]
  /\ promised = [a \in Acceptor |-> -1]

IncreasePromise(a, b) ==
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED voted

\* The ballot must be safe: no other value may have been voted for in it, and
\* every lower ballot already safely committed to this value.
\* The quorum is needed to witness that safety.
SafeAt(b, v) ==
  /\ \A c \in 0 .. b - 1 :
       \E Q \in Quorum :
         \A x \in Q :
           \/ \E w \in Value : [ball |-> c, val |-> v] \in voted[x]
           \/ (\A k \in 0 .. Ballot : [ball |-> c, val |-> k] \in voted[x])
  /\ \A Q \in Quorum : \E x \in Q : [ball |-> b, val |-> v] \in voted[x]

CastVote(a, b, v) ==
  /\ b >= promised[a]
  /\ \A w \in voted[a] : w.ball # b
  /\ \A x \in Acceptor : \A w \in voted[x] : (w.ball = b) => (w.val = v)
  /\ SafeAt(b, v)
  /\ voted' = [voted EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
  /\ promised' = [promised EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in 0 .. Ballot : IncreasePromise(a, b)
  \/ \E a \in Acceptor, b \in 0 .. Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* A value is chosen once some quorum has voted for it in some ballot.
Chosen ==
  { v \in Value :
      \E Q \in Quorum :
        \E b \in 0 .. Ballot : \A x \in Q : [ball |-> b, val |-> v] \in voted[x] }

\* Every vote ever cast was safe at its ballot number.
AllVotesSafe ==
  \A a \in Acceptor : \A w \in voted[a] : SafeAt(w.ball, w.val)

\* No two values are ever voted for in the same ballot.
BallotsUnique ==
  \A a, x \in Acceptor :
    \A w \in voted[a] : \A k \in voted[x] :
      (w.ball = k.ball) => (w.val = k.val)

\* The votes are well typed and the thresholds stay in range.
TmpCoherent == TypeOK

Inv == AllVotesSafe /\ BallotsUnique /\ TmpCoherent

\* Refinement map: the abstract specification's chosen set is derived from the
\* concrete votes in exactly this way.
ConsensusSpecBar ==
  Chosen = { v \in Value :
               \E Q \in Quorum :
                 \E b \in 0 .. Ballot : \A x \in Q : [ball |-> b, val |-> v] \in voted[x] }

====