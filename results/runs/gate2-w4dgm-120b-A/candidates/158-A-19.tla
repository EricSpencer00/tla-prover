---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

(* A high-level Paxos-style consensus algorithm.  A value is chosen when a     *)
(* quorum of acceptors have all voted for it in the same ballot, and the       *)
(* safety invariant protects against two different values ever being chosen.  *)

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* The model checker will bind MCAcceptor, MCValue, MCQuorum and MCBallot to
\* concrete finite instantiations in the .cfg file; they are defined here as
\* operators so the substitution is semantics-preserving, not syntactic.

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

NoVote == [ball |-> 0, val |-> CHOOSE w \in Value : TRUE]

VARIABLES votes, thresh, voted

vars == << votes, thresh, voted >>

TypeOK ==
    /\ votes \in [MCAcceptor -> SUBSET [ball : MCBallot, val : MCValue]]
    /\ thresh \in [MCAcceptor -> MCBallot \cup {-1}]
    /\ voted \in [MCAcceptor -> [ball : MCBallot, val : MCValue]]

Init ==
    /\ votes = [a \in MCAcceptor |-> {}]
    /\ thresh = [a \in MCAcceptor |-> -1]
    /\ voted = [a \in MCAcceptor |-> NoVote]

\* Raising the promise threshold is how an acceptor refuses to vote in
\* earlier ballots; it alone does not cast a vote.
RaiseThreshold(a, b) ==
    /\ b > thresh[a]
    /\ thresh' = [thresh EXCEPT ![a] = b]
    /\ UNCHANGED << votes, voted >>

VotedIn(b) == {a \in MCAcceptor : \E w \in votes[a] : w.ball = b}

\* A value is safe at ballot b only if every lower ballot already had a
\* quorum voting for that same value (or is now unwinnable).
SafeAt(v, b) ==
    /\ \A c \in MCBallot : c < b =>
         \E Q \in MCQuorum :
            \A a \in Q :
               \/ \E w \in votes[a] : w.ball = c /\ w.val = v
               \/ \A w \in votes[a] : w.ball # c
    /\ \A Q \in MCQuorum : \A a \in Q : \A w \in votes[a] : w.ball <= b

Vote(a, v, b) ==
    /\ b >= thresh[a]
    /\ \A w \in votes[a] : w.ball # b
    /\ \A c \in MCBallot : \A d \in MCAcceptor :
          (c = b /\ d \in VotedIn(b) /\ votes[d] # {}) => votes[d] = v
    /\ SafeAt(v, b)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ball |-> b, val |-> v]}]
    /\ voted' = [voted EXCEPT ![a] = [ball |-> b, val |-> v]]
    /\ thresh' = [thresh EXCEPT ![a] = b]

QuorumChoice(v) == \E Q \in MCQuorum : \A a \in Q : voted[a].val = v

Next ==
    \/ \E a \in MCAcceptor, b \in MCBallot : RaiseThreshold(a, b) \/ Vote(a, CHOOSE v \in MCValue : TRUE, b)
    \/ \E a \in MCAcceptor, v \in MCValue, b \in MCBallot : Vote(a, v, b)

Spec == Init /\ [][Next]_vars

QuorumChoiceIsUnique ==
    \A v1, v2 \in MCValue : (QuorumChoice(v1) /\ QuorumChoice(v2)) => v1 = v2

AllVotesAreSafe ==
    \A a \in MCAcceptor : \A w \in votes[a] : SafeAt(w.val, w.ball)

AtMostOneValuePerBallot ==
    \A c \in MCBallot : \A a, d \in MCAcceptor :
        (\A w \in votes[a] : w.ball = c) /\ (\A w \in votes[d] : w.ball = c) => votes[a] = votes[d]

Inv == QuorumChoiceIsUnique /\ AllVotesAreSafe /\ AtMostOneValuePerBallot

\* The voting algorithm refines the abstract consensus spec: a value is
\* chosen exactly when every acceptor in some quorum has voted for it.
ConsensusSpecBar == \A v \in MCValue : QuorumChoice(v) => \A Q \in MCQuorum : \A a \in Q : voted[a].val = v

\* Swapping two acceptors throughout the system is a symmetry, so every such
\* automorphism of the acceptor set must preserve the transition relation.
MCSymmetry ==
    { f \in [MCAcceptor -> MCAcceptor] ->
        /\ \A a \in MCAcceptor : f[a] \in MCAcceptor
        /\ \A a, b \in MCAcceptor : (f[a] = f[b]) => (a = b)
        /\ \A a \in MCAcceptor :
              /\ votes' = [votes EXCEPT ![f[a]] = votes[a]]
              /\ voted' = [voted EXCEPT ![f[a]] = voted[a]]
              /\ thresh' = [thresh EXCEPT ![f[a]] = thresh[a]]
    }

====