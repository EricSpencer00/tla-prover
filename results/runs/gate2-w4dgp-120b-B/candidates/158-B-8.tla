---- MODULE Voting ----
EXTENDS Integers

CONSTANTS Value, Acceptor, Quorum

\* At most one value is chosen total, and a value is only ever
\* chosen in one ballot, even though the algorithm presents ballot
\* numbers in no particular order.  The algorithm's safety is
\* therefore derived from the runtime ordering of votes, not from
\* any ordering of ballot numbers.
THEOREM AtMostOneChosen == \A a, b \in Value : [a = b] =>
  /\ \A p \in Quorum : p \subseteq Acceptor
  /\ \A p \in Quorum : p # {}

Ballot == Nat

VARIABLES votes, maxBal

TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

VotedFor(a, b, v) == <<b, v>> \in votes[a]

\* A quorum voted for v in ballot b.
ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

\* An acceptor's votes are only valid in ballots >= maxBal[a].
DidNotVoteAt(a, b) ==
  \A v \in Value : ~VotedFor(a, b, v)

CannotVoteAt(a, b) ==
  /\ maxBal[a] > b
  /\ DidNotVoteAt(a, b)

NoneOtherChoosableAt(b, v) ==
  \E Q \in Quorum :
    \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)

\* Nothing other than v has been or can be chosen in ballot < b.
SafeAt(b, v) ==
  \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)

\* A ballot's votes are only cast by voters who can
\* also cast votes in later ballots.
ShowsSafeAt(Q, b, v) ==
  /\ \A a \in Q : maxBal[a] >= b
  /\ \E c \in -1..(b-1) :
       /\ c # -1 => \E a \in Q : VotedFor(a, c, v)
       /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)

Init == /\ votes = [a \in Acceptor |-> {}]
        /\ maxBal = [a \in Acceptor |-> -1]

IncreaseMaxBal(a, b) ==
  /\ b > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* The last conjunct preserves that no ballot can later be cast for
\* a value other than v -- that would undo the ballot's safety.
VoteFor(a, b, v) ==
  /\ maxBal[a] <= b
  /\ \A vt \in votes[a] : vt[1] # b
  /\ \A Q \in Quorum : ShowsSafeAt(Q, b, v)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ maxBal' = [maxBal EXCEPT ![a] = b]

Next == \E a \in Acceptor, b \in Ballot :
          IncreaseMaxBal(a, b) \/ \E v \in Value : VoteFor(a, b, v)

Spec == Init /\ [][Next]_<<votes, maxBal>>

\* No ballot can be cast for a value other than whichever value
\* that ballot's votes make safe.  That restriction is exactly what
\* stops the same ballot from ever backing a second value.
VotesSafe == \A a \in Acceptor, b \in Ballot, v \in Value :
               VotedFor(a, b, v) => SafeAt(b, v)

\* A single ballot can never be cast for two different values.
OneVote == \A a \in Acceptor, b \in Ballot, v, w \in Value :
             VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)

Inv == TypeOK /\ VotesSafe /\ OneVote

=============================================================================