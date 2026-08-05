---- MODULE Voting ----
EXTENDS Integers, TLAPS
CONSTANTS Value, Acceptor, Quorum
ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
                         \* Every two quorums overlap, so no two values
                         \* can both win a quorum.
THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}

Ballot == Nat
VARIABLES votes, maxBal
TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

\* Definition VotedFor must be a syntactic abbreviation, so it can be
\* unfolded when TLC expands the invariant Inv.  The rest of the
\* definitions are theorems that read better as separate assumptions.
VotedFor(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)
chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}
DidNotVoteAt(a, b) == \A v \in Value : ~VotedFor(a, b, v)
CannotVoteAt(a, b) == /\ maxBal[a] > b
                      /\ DidNotVoteAt(a, b)

\* If a quorum has voted or can never vote for a value v in ballot b,
\* then no other value can ever win a quorum in that ballot.
NoneOtherChoosableAt(b, v) ==
  \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)
SafeAt(b, v) == \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)

THEOREM AllSafeAtZero == \A v \in Value : SafeAt(0, v)
THEOREM ChoosableThm ==
  \A b \in Ballot, v \in Value : ChosenAt(b, v) => NoneOtherChoosableAt(b, v)

\* The quorums are formed before the voting begins, so this is an
\* invariant of the algorithm, not an assumption about Quorum.
VotesSafe == \A a \in Acceptor, b \in Ballot, v \in Value :
               VotedFor(a, b, v) => SafeAt(b, v)

OneVote == \A a \in Acceptor, b \in Ballot, v, w \in Value :
              VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)

OneValuePerBallot == \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
                       (VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2)) => (v1 = v2)
THEOREM OneValuePerBallot => OneVote

\* Theorem VotesSafeImpliesConsistency: once a value has been chosen,
\* every other value has already been prevented from ever being chosen.
THEOREM VotesSafeImpliesConsistency ==
  /\ TypeOK /\ VotesSafe /\ OneVote
  => \/ chosen = {}
     \/ \E v \in Value : chosen = {v}
THEOREM ShowsSafety ==
  /\ TypeOK /\ VotesSafe /\ OneValuePerBallot
  => \A Q \in Quorum, b \in Ballot, v \in Value :
       /\ \A a \in Q : maxBal[a] >= b
       /\ \A c \in 0..b, a \in Q : (c < b) => DidNotVoteAt(a, c)
       => SafeAt(b, v)

Init == /\ votes = [a \in Acceptor |-> {}]
        /\ maxBal = [a \in Acceptor |-> -1]

IncreaseMaxBal(a, b) ==
  /\ b > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* VoteFor is enabled only when the vote would preserve OneValuePerBallot,
\* so the invariant is not used to justify it.
VoteFor(a, b, v) ==
  /\ maxBal[a] <= b
  /\ \A vt \in votes[a] : vt[1] # b
  /\ \A c \in Acceptor \ {a} :
       \A vt \in votes[c] : vt[1] = b => vt[2] = v
  /\ \A Q \in Quorum : \A a \in Q : maxBal[a] >= b
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ maxBal' = [maxBal EXCEPT ![a] = b]

Next == \E a \in Acceptor, b \in Ballot :
          \/ IncreaseMaxBal(a, b)
          \/ \E v \in Value : VoteFor(a, b, v)

Spec == Init /\ [][Next]_<<votes, maxBal>>
Inv == TypeOK /\ VotesSafe /\ OneValuePerBallot

=============================================================================