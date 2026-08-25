---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(***************************************************************************)
(*  Operators that map the abstract constants to the concrete model sets   *)
(***************************************************************************)

MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

(***************************************************************************)
(*  State variables                                                       *)
(***************************************************************************)

VARIABLES votes, thresh

(***************************************************************************)
(*  Helper definitions                                                    *)
(***************************************************************************)

(* a vote is a pair <<ballot, value>>                         *)
VotePair == <<Ballot, Value>>

(* the set of all votes cast by an acceptor a *)
VotesOf(a) == votes[a]

(* the current promise threshold of acceptor a *)
ThreshOf(a) == thresh[a]

(*  The predicate “safe” : a value v is safe at ballot b iff
    for every lower ballot c (< b) there is a quorum Q such that
    each acceptor in Q either has already voted (c, v) or
    can never vote in ballot c (i.e., its threshold > c).               *)
Safe(b, v) ==
  \A c \in Ballot :
    (c < b) => 
      \E Q \in Quorum :
        \A a \in Q :
          (<<c, v>> \in votes[a]) \/ (c < thresh[a])

(*  A value is chosen when some quorum has all its members
    voting for that value in the same ballot.                         *)
Chosen(v) ==
  \E b \in Ballot :
    \E Q \in Quorum :
      \A a \in Q : <<b, v>> \in votes[a]

(***************************************************************************)
(*  Initialization                                                         *)
(***************************************************************************)

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thresh = [a \in Acceptor |-> -1]

(***************************************************************************)
(*  Actions                                                                *)
(***************************************************************************)

(*  Promise action: acceptor a raises its threshold to a higher ballot b *)
Promise(a, b) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ b > thresh[a]
  /\ UNCHANGED votes
  /\ thresh' = [thresh EXCEPT ![a] = b]

(*  Vote action: acceptor a votes for value v in ballot b *)
Vote(a, b, v) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ v \in Value
  /\ b >= thresh[a]                                 \* not below promise
  /\ ~(\E p \in votes[a] : p[1] = b)                \* hasn't voted in b yet
  /\ \A a2 \in Acceptor :
        (\E p \in votes[a2] : p[1] = b) => 
          (\A p \in votes[a2] : p[1] = b => p[2] = v)   \* no conflicting vote
  /\ Safe(b, v)                                    \* safety condition
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
  /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
  \E a \in Acceptor :
    (\E b \in Ballot : Promise(a, b))
    \/ (\E b \in Ballot, v \in Value : Vote(a, b, v))

(***************************************************************************)
(*  Specification                                                          *)
(***************************************************************************)

Spec == Init /\ [][Next]_<<votes, thresh>>

(***************************************************************************)
(*  Invariant                                                              *)
(***************************************************************************)

(*  Type correctness of votes and thresholds                         *)
TypeInv ==
  /\ \A a \in Acceptor : votes[a] \subseteq Ballot \X Value
  /\ \A a \in Acceptor : thresh[a] \in Ballot \cup {-1}

(*  No two different values are voted for in the same ballot          *)
OneValuePerBallot ==
  \A b \in Ballot :
    \A v1, v2 \in Value :
      ( (\E a1 \in Acceptor : <<b, v1>> \in votes[a1]) /\ 
        (\E a2 \in Acceptor : <<b, v2>> \in votes[a2]) ) => v1 = v2

(*  Every vote that has been cast is safe at its ballot                *)
SafetyInv ==
  \A a \in Acceptor :
    \A p \in votes[a] :
      Safe(p[1], p[2])

Inv == TypeInv /\ OneValuePerBallot /\ SafetyInv

(***************************************************************************)
(*  Property: at most one value can be chosen                             *)
(***************************************************************************)

ConsensusSpecBar == 
  \A v1, v2 \in Value :
    (Chosen(v1) /\ Chosen(v2)) => v1 = v2

(***************************************************************************)
(*  Symmetry: permutations of acceptors preserving quorums                *)
(***************************************************************************)

Permutation(f) ==
  /\ f \in [Acceptor -> Acceptor]
  /\ \A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2   \* bijection

PermPreservesQuorums(f) ==
  \A Q \in Quorum : { f[a] : a \in Q } \in Quorum

MCSymmetry ==
  { f \in [Acceptor -> Acceptor] : 
      /\ Permutation(f)
      /\ PermPreservesQuorums(f) }

=============================================================================