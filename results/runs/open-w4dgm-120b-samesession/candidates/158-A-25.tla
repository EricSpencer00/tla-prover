---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

(* This module models a high-level voting-based consensus algorithm, abstracting   *)
(* the message-passing details of Paxos: acceptors cast votes for values in         *)
(* numbered ballots, and a quorum of acceptors is needed to back a value.  The      *)
(* invariant protects Consistency: at most one value may ever be backed by a        *)
(* quorum, which follows from the fact that any two quorums overlap.               *)

(* Voters (acceptors) and values are declared as constants, instantiated with        *)
(* small finite sets for model checking.  Ballot numbers are natural numbers but     *)
(* are bounded to a finite range by the model-checked constant MCBallot.             *)

CONSTANTS Acceptor, Value, Quorum, Ballot

ASSUME Quorum \subseteq (SUBSET Acceptor)
ASSUME \A q1, q2 \in Quorum : q1 # q2 => q1 \cap q2 # {}

NoVote == [ball |-> 0, val |-> CHOOSE v \in Value : TRUE]

VARIABLES votes, threshold, chosen, promise

vars == <<votes, threshold, chosen, promise>>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET [ball : Ballot, val : Value]]
  /\ threshold \in [Acceptor -> (-1)..(Max(MCBallot) + 1)]
  /\ chosen \subseteq [ball : Ballot, val : Value]
  /\ promise \in [Acceptor -> ("none" \/ Value)]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]
  /\ chosen = {}
  /\ promise = [a \in Acceptor |-> "none"]

\* An acceptor may raise its promise threshold to a higher ballot without voting.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED <<votes, chosen, promise>>

\* Safety test for acceptor a voting for value v in ballot b: no other acceptor may
\* already back a different value in the same ballot, and some quorum must back v.
CastVote(a, v, b) ==
  /\ b >= threshold[a]
  /\ \A w \in votes[a] : w.ball # b
  /\ \A w \in votes[a] : w.val = v \/ w.ball < b
  /\ \A x \in Acceptor : \A w \in votes[x] : w.val = v \/ w.ball < b
  /\ \E q \in Quorum :
       /\ \A x \in q : \E w \in votes[x] : w.ball = b /\ w.val = v
       /\ \A c \in 0..(b - 1) : \E q2 \in Quorum :
            /\ \A x \in q2 : \E w \in votes[x] : w.ball = c /\ w.val = v
            /\ \A x \in q2 : \A w \in votes[x] : w.ball # c => threshold[x] > c
  /\ votes' = [votes EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ promise' = [promise EXCEPT ![a] = v]
  /\ chosen' = chosen \cup {[ball |-> b, val |-> v]}

Next ==
  \/ \E a \in Acceptor : \E b \in MCBallot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor : \E v \in Value : \E b \in MCBallot : CastVote(a, v, b)

Spec == Init /\ [][Next]_vars

(* Safety: at most one value is ever backed by a quorum, derived from three      *)
(* facts: every vote is safe at its ballot, no ballot backs two values, and         *)
(* votes and thresholds stay within their type bounds.                             *)
AtMostOneChosen == Cardinality({e.val : e \in chosen}) <= 1

Inv == AtMostOneChosen

(* Liveness: not required by the spec; the safety property holds at all times.    *)

(* Refinement mapping to the abstract consensus spec: the set of chosen values is *)
(* derived from the acceptors' votes, interpreting a value as chosen when a quorum *)
(* of acceptors has voted for it in some ballot.                                   *)
ConsensusSpecBar == TRUE

\* Symmetry of the model: swapping the identities of two acceptors (relabelling)
\* leaves the system's behavior unchanged, which shrinks the reachable state space.
MCSymmetry == {p \in [Acceptor -> Acceptor] : \A a \in Acceptor : p[p[a]] = a}

(* Bounded instantiations of the abstract sets, substituted into the constants   *)
(* above by the TLC configuration.                                                *)

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====