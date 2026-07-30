---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold
vars == <<votes, threshold>>

Voter == Acceptor \X Value \X Ballot
Occurred(v) == \E x \in Acceptor : <<x, v, 0>> \in votes

TypeOK ==
  /\ votes \subseteq Voter
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = {}
  /\ threshold = [x \in Acceptor |-> -1]

\* An acceptor raises its promise threshold, refusing to vote below it.
Raise(x, b) ==
  /\ b > threshold[x]
  /\ threshold' = [threshold EXCEPT ![x] = b]
  /\ UNCHANGED votes

\* A vote for v in ballot b is allowed only if it is safe at b, which means
\* that every lower ballot is already safe for v. Casting a vote also raises
\* the acceptor's threshold to b, sealing the ballot choice.
Vote(x, v, b) ==
  /\ b >= threshold[x]
  /\ ~Occurred(v)
  /\ \A w \in Value : w # v => ~Occurred(w)
  /\ \A c \in 0..(b - 1) :
       \E q \in Quorum :
         /\ \A y \in q : (<<y, v, c>> \in votes) \/ threshold[y] > c
         /\ \A y \in q : threshold[y] # c
  /\ votes' = votes \cup {<<x, v, b>>}
  /\ threshold' = [threshold EXCEPT ![x] = b]

Next ==
  \/ \E x \in Acceptor, b \in Ballot : Raise(x, b)
  \/ \E x \in Acceptor, v \in Value, b \in Ballot : Vote(x, v, b)

Spec == Init /\ [][Next]_vars

\* Every cast vote is safe at its ballot number, so each ballot is backed by
\* a quorum that already agreed on the same value at every lower ballot.
EveryVoteIsSafe ==
  \A e \in votes :
    \A c \in 0..(e[2] - 1) :
      \E q \in Quorum :
        /\ \A y \in q : (<<y, e[1], c>> \in votes) \/ threshold[y] > c
        /\ \A y \in q : threshold[y] # c

AtMostOneValuePerBallot ==
  \A b \in Ballot : \A x, y \in Value : (Occurred(x) /\ Occurred(y)) => x = y

ConsensusSpecBar == EveryVoteIsSafe /\ AtMostOneValuePerBallot /\ TypeOK

====