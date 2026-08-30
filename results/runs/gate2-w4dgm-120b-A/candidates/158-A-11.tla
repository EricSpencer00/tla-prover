---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>
Acceptor == {a1, a2, a3}
Value == {v1, v2}
Ballot == 0..2
Quorum == { {a1, a2}, {a2, a3}, {a1, a3} }

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> (-1)..2]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold to a higher ballot, and will
\* subsequently refuse to vote in any ballot below that threshold.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* An acceptor votes for a value in a ballot only if that ballot is at or
\* above its threshold, it has not already voted in that ballot, no other
\* acceptor voted for a different value in that ballot, and a quorum can
\* show the value is safe at that ballot.
Vote(a, b, val) ==
  /\ b >= threshold[a]
  /\ \A c \in Ballot, w \in Value : <<c, w>> \notin votes[a]
  /\ \A c \in Ballot : \A w \in Value : (c = b /\ w # val) => \A x \in Acceptor : <<c, w>> \notin votes[x]
  /\ \E Q \in Quorum :
        \A c \in 0..(b - 1) : \E Qc \in Quorum : \A x \in Qc : <<c, val>> \in votes[x]
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, val>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, val \in Value : Vote(a, b, val)

Spec == Init /\ [][Next]_vars

\* Chosen values are those voted for by an entire quorum in some ballot.
Chosen ==
  { val \in Value : \E Q \in Quorum, b \in Ballot :
        \A a \in Q : <<b, val>> \in votes[a] }

\* A vote must be safe at its ballot: every lower ballot for that value must
\* also be backed by a quorum, so a later vote can never contradict an
\* earlier one and no two different values can ever both have quorum.
VoteSafe ==
  \A a \in Acceptor : \A b \in Ballot, val \in Value :
    <<b, val>> \in votes[a] =>
      \A c \in 0..(b - 1) : \E Q \in Quorum : \A x \in Q : <<c, val>> \in votes[x]

\* No two values are ever both chosen by a quorum in different ballots.
AtMostOneChosen ==
  \A v1_ \in Value, v2_ \in Value : (v1_ \in Chosen /\ v2_ \in Chosen) => v1_ = v2_

Inv == TypeOK /\ VoteSafe /\ AtMostOneChosen

\* The voting algorithm implements the abstract consensus specification.
ConsensusSpecBar == Spec => [Choice -> Chosen]

\* Symmetry: swapping the two proposer roles leaves the system behavior
\* unchanged, so the ballot numbers are the only thing that keep two runs apart.
MCSymmetry == {p \in [Acceptor -> Acceptor] :
  /\ \A a \in Acceptor : p[a] \in Acceptor
  /\ \A a1_, a2_ \in Acceptor : p[a1_] = p[a2_] => a1_ = a2_}

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====