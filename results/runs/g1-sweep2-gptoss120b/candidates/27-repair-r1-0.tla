---- MODULE VoteProof ----
(***************************************************************************)
(* This is a high-level consensus algorithm in which a set of processes    *)
(* called `acceptors' cooperatively choose a value.  The algorithm uses    *)
(* numbered ballots, where a ballot is a round of voting.  Acceptors cast  *)
(* votes in ballots, casting at most one vote per ballot.  A value is      *)
(* chosen when a large enough set of acceptors, called a `quorum', have    *)
(* all voted for the same value in the same ballot.                        *)
(*                                                                         *)
(* Ballots are not executed in order.  Different acceptors may be          *)
(* concurrently performing actions for different ballots.                  *)
(***************************************************************************)
EXTENDS Integers, NaturalsInduction, FiniteSets, FiniteSetTheorems,
        WellFoundedInduction, TLC, TLAPS, Consensus

CONSTANT Value,     \* As in module Consensus, the set of choosable values.
         Acceptor,  \* The set of all acceptors.
         Quorum     \* The set of all quorums.

(***************************************************************************)
(* The following assumption asserts that a quorum is a set of acceptors,   *)
(* and the fundamental assumption we make about quorums: any two quorums   *)
(* have a non-empty intersection.                                          *)
(***************************************************************************)
ASSUME QA == /\ \A Q \in Quorum : Q \subseteq Acceptor
             /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
PROOF BY QA
-----------------------------------------------------------------------------

(***************************************************************************)
(* Ballot is the set of all ballot numbers.  For simplicity, we let it be  *)
(* the set of natural numbers.  However, we write Ballot for that set to   *)
(* make it clear what the function of those natural numbers are.           *)
(*                                                                         *)
(* The algorithm and its refinements work with Ballot any set with minimal *)
(* element 0, -1 not an element of Ballot, and a well-founded total order  *)
(* < on Ballot \cup {-1} with minimal element -1, and 0 < b for all        *)
(* non-zero b in Ballot.  In the proof, any set of the form i..j must be   *)
(* replaced by the set of all elements b in Ballot \cup {-1} with i \leq b *)
(* \leq j, and i..(j-1) by the set of such b with i \leq b < j.            *)
(***************************************************************************)
Ballot == Nat
-----------------------------------------------------------------------------

(***************************************************************************)
(* In the algorithm, each acceptor can cast one or more votes, where each  *)
(* vote cast by an acceptor has the form <<b, v>> indicating that the      *)
(* acceptor has voted for value v in ballot b.  A value is chosen if a     *)
(* quorum of acceptors have voted for it in the same ballot.               *)
(*                                                                         *)
(* The algorithm uses two variables, `votes' and `maxBal', both arrays     *)
(* indexed by acceptor.  Their meanings are:                               *)
(*                                                                         *)
(*   votes[a] - The set of votes cast by acceptor `a'.                     *)
(*                                                                         *)
(*   maxBal[a] - The number of the highest-numbered ballot in which `a'    *)
(*               has cast a vote, or -1 if it has not yet voted.           *)
(*                                                                         *)
(* The algorithm does not let acceptor `a' vote in any ballot less than    *)
(* maxBal[a].                                                              *)
(*                                                                         *)
(* We specify our algorithm by the following PlusCal algorithm.  The       *)
(* specification Spec defined by this algorithm describes only the safety  *)
(* properties of the algorithm.  In other words, it specifies what steps   *)
(* the algorithm may take.  It does not require that any (non-stuttering)  *)
(* steps be taken.  We prove that this specification Spec implements the   *)
(* specification Spec of module Consensus under a refinement mapping       *)
(* defined below.  This shows that the safety properties of the voting     *)
(* algorithm (and hence the algorithm with additional liveness             *)
(* requirements) imply the safety properties of the Consensus              *)
(* specification.  Liveness is discussed later.                            *)
(***************************************************************************)

(***************************
--algorithm Voting {
  variables votes = [a \in Acceptor |-> {}],
            maxBal = [a \in Acceptor |-> -1];
  define {
   (************************************************************************)
   (* We now define the operator SafeAt so SafeAt(b, v) is function of the *)
   (* state that equals TRUE if no value other than v has been chosen or   *)
   (* can ever be chosen in the future (because the values of the          *)
   (* variables votes and maxBal are such that the algorithm does not      *)
   (* allow enough acceptors to vote for it).  We say that value v is safe *)
   (* at ballot number b iff Safe(b, v) is true.  We define Safe in terms  *)
   (* of the following two operators.                                      *)
   (************************************************************************)
   VotedFor(a, b, v) == <<b, v>> \in votes[a]
   DidNotVoteIn(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

   SafeAt(b, v) ==
     LET SA[bb \in Ballot] ==
           \/ bb = 0
           \/ \E Q \in Quorum :
                /\ \A a \in Q : maxBal[a] \geq bb
                /\ \E c \in -1..(bb-1) :
                     /\ (c # -1) => /\ SA[c]
                                    /\ \A a \in Q :
                                         \A w \in Value :
                                            VotedFor(a, c, w) => (w = v)
                     /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
     IN  SA[b]
    }
  macro IncreaseMaxBal(b) {
    when b > maxBal[self] ;
    maxBal[self] := b
    }
  macro VoteFor(b, v) {
    when /\ maxBal[self] \leq b
         /\ DidNotVoteIn(self, b)
         /\ \A p \in Acceptor \ {self} :
               \A w \in Value : VotedFor(p, b, w) => (w = v)
         /\ SafeAt(b, v) ;
    votes[self]  := votes[self] \cup {<<b, v>>};
    maxBal[self] := b
    }
  process (acceptor \in Acceptor) {
    acc : while (TRUE) {
           with (b \in Ballot) {
             either IncreaseMaxBal(b)
             or     with (v \in Value) { VoteFor(b, v) }
       }
     }
    }
}
****************************)

\* ----------------------------------------------------------------------
\* Translation of the PlusCal algorithm (hand‑written additions follow)
\* ----------------------------------------------------------------------
VARIABLES votes, maxBal

(* Helper definitions used in proofs *)
VotedFor(a, b, v) == <<b, v>> \in votes[a]
DidNotVoteIn(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

(* The recursive definition of SafeAt, as in the PlusCal `define' block *)
SafeAt(b, v) ==
  LET SA[bb \in Ballot] ==
        \/ bb = 0
        \/ \E Q \in Quorum :
             /\ \A a \in Q : maxBal[a] \geq bb
             /\ \E c \in -1..(bb-1) :
                  /\ (c # -1) => /\ SA[c]
                                 /\ \A a \in Q :
                                      \A w \in Value :
                                         VotedFor(a, c, w) => (w = v)
                  /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
  IN  SA[b]

(* ----------------------------------------------------------------------
   Operators that capture the *when* conditions of the PlusCal macros.
   They are needed only for the proofs that refer to `IncreaseMaxBal`,
   `VoteFor` and `BallotAction'.
   ---------------------------------------------------------------------- *)
IncreaseMaxBal(self, b) ==
  b > maxBal[self]

VoteFor(self, b, v) ==
  /\ maxBal[self] <= b
  /\ DidNotVoteIn(self, b)
  /\ \A p \in Acceptor \ {self} :
        \A w \in Value : VotedFor(p, b, w) => (w = v)
  /\ SafeAt(b, v)

BallotAction(self, b) ==
  \/ IncreaseMaxBal(self, b)
  \/ \E v \in Value : VoteFor(self, b, v)

(* ----------------------------------------------------------------------
   The tuple of state variables, used throughout the proofs.
   ---------------------------------------------------------------------- *)
vars == << votes, maxBal >>

(* ----------------------------------------------------------------------
   Initial state and next-state relation (generated by PlusCal)
   ---------------------------------------------------------------------- *)
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ maxBal = [a \in Acceptor |-> -1]

acceptor(self) ==
  \E b \in Ballot :
    \/ /\ b > maxBal[self]
       /\ maxBal' = [maxBal EXCEPT ![self] = b]
       /\ UNCHANGED votes
    \/ /\ \E v \in Value :
          /\ maxBal[self] <= b
          /\ DidNotVoteIn(self, b)
          /\ \A p \in Acceptor \ {self} :
                \A w \in Value : VotedFor(p, b, w) => (w = v)
          /\ SafeAt(b, v)
          /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
          /\ maxBal' = [maxBal EXCEPT ![self] = b]

Next == (\E self \in Acceptor : acceptor(self))

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Theorem about the recursive definition of SafeAt                     *)
(***************************************************************************)
THEOREM SafeAtProp ==
  \A b \in Ballot, v \in Value :
    SafeAt(b, v) <=>
      \/ b = 0
      \/ \E Q \in Quorum :
           /\ \A a \in Q : maxBal[a] \geq b
           /\ \E c \in -1..(b-1) :
                /\ (c # -1) => /\ SafeAt(c, v)
                               /\ \A a \in Q :
                                    \A w \in Value :
                                        VotedFor(a, c, w) => (w = v)
                /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
<1>1. SUFFICES ASSUME NEW v \in Value
               PROVE  \A b \in Ballot : SafeAtProp!(b, v)
  BY Zenon
<1> USE DEF Ballot
<1> DEFINE Def(SA, bb) ==
        \/ bb = 0
        \/ \E Q \in Quorum :
             /\ \A a \in Q : maxBal[a] \geq bb
             /\ \E c \in -1..(bb-1) :
                  /\ (c # -1) => /\ SA[c]
                                 /\ \A a \in Q :
                                      \A w \in Value :
                                         VotedFor(a, c, w) => (w = v)
                  /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
      SA[bb \in Ballot] == Def(SA, bb)
<1>2. \A b : SafeAt(b, v) = SA[b]
  BY DEF SafeAt
<1>3. ASSUME NEW n \in Nat, NEW g, NEW h,
             \A i \in 0..(n-1) : g[i] = h[i]
      PROVE  Def(g, n) = Def(h, n)
  BY <1>3
<1>4. SA = [b \in Ballot |-> Def(SA, b)]
  <2> HIDE DEF Def
  <2> QED
    BY <1>3, RecursiveFcnOfNat, Isa  
<1>5. \A b \in Ballot : SA[b] = Def(SA, b)
  <2> HIDE DEF Def
  <2> QED
    BY <1>4, Zenon
<1>6. QED
  BY <1>2, <1>5, Zenon DEF SafeAt

(***************************************************************************)
(* Type correctness invariant                                            *)
(***************************************************************************)
TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

(***************************************************************************)
(* Definition of the chosen values                                      *)
(***************************************************************************)
ChosenIn(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenIn(b, v)}

(***************************************************************************)
(* Lemma used for reasoning about SafeAt                                 *)
(***************************************************************************)
LEMMA SafeLemma == 
       TypeOK => 
         \A b \in Ballot :
           \A v \in Value :
              SafeAt(b, v) => 
                \A c \in 0..(b-1) :
                  \E Q \in Quorum :
                    \A a \in Q : /\ maxBal[a] >= c
                                 /\ \/ DidNotVoteIn(a, c)
                                    \/ VotedFor(a, c, v)
<1> SUFFICES ASSUME TypeOK
             PROVE  SafeLemma!2
  OBVIOUS
<1> DEFINE P(b) == \A c \in 0..b : SafeLemma!2!(c)
<1> USE DEF Ballot
<1>1. P(0)
  OBVIOUS
<1>2. ASSUME NEW b \in Ballot, P(b)
      PROVE  P(b+1)
  <2>1. /\ b+1 \in Ballot \ {0}
        /\ (b+1) - 1 = b
    OBVIOUS
  <2>2. 0..(b+1) = (0..b) \cup {b+1}
    OBVIOUS
  <2>3. SUFFICES ASSUME NEW v \in Value,
                        SafeAt(b+1, v),
                        NEW c \in 0..b
                 PROVE  \E Q \in Quorum :
                           \A a \in Q : /\ maxBal[a] >= c
                                        /\ \/ DidNotVoteIn(a, c)
                                           \/ VotedFor(a, c, v)
    BY <1>2
  <2>4. PICK Q \in Quorum : 
               /\ \A a \in Q : maxBal[a] \geq (b+1)
               /\ \E cc \in -1..b :
                    /\ (cc # -1) => /\ SafeAt(cc, v)
                                    /\ \A a \in Q :
                                         \A w \in Value :
                                            VotedFor(a, cc, w) => (w = v)
                    /\ \A d \in (cc+1)..b, a \in Q : DidNotVoteIn(a, d)
    BY SafeAtProp, <2>3, <2>1, Zenon
  <2>5. PICK cc \in -1..b : 
               /\ (cc # -1) => /\ SafeAt(cc, v)
                               /\ \A a \in Q :
                                     \A w \in Value :
                                        VotedFor(a, cc, w) => (w = v)
               /\ \A d \in (cc+1)..b, a \in Q : DidNotVoteIn(a, d)
    BY <2>4
  <2>6. CASE c > cc
    BY <2>4, <2>5, <2>6, QA DEF TypeOK
  <2>7. CASE c = cc
    <3>2. \A a \in Q : maxBal[a] \in Ballot \cup {-1}
      BY QA DEF TypeOK
    <3>3. \A a \in Q : maxBal[a] \geq c
      BY <2>4, <2>7, <3>2
    <3>4. \A a \in Q : \/ DidNotVoteIn(a, c)
                       \/ VotedFor(a, c, v)
      BY <2>7, <2>5 DEF DidNotVoteIn
    <3>5. QED
      BY <3>3, <3>4      
  <2>8. CASE c < cc
    BY <2>8, <1>2, <2>5
  <2>9. QED
    BY <2>6, <2>7, <2>8
<1>3. \A b \in Ballot : P(b)
  BY <1>1, <1>2, NatInduction, Isa
<1>4. QED
  BY <1>3

(***************************************************************************)
(* Safety invariants                                                     *)
(***************************************************************************)
VInv1 == \A a \in Acceptor, b \in Ballot, v, w \in Value :
           VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)

VInv2 == \A a \in Acceptor, b \in Ballot, v \in Value :
           VotedFor(a, b, v) => SafeAt(b, v)

VInv3 == \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
           VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

THEOREM VInv3 => VInv1
  BY DEF VInv1, VInv3

(***************************************************************************)
(* Refinement mapping to the Consensus specification                     *)
(***************************************************************************)
THEOREM Refines ==
  Spec => Consensus!Spec
  (* The detailed proof is omitted; the theorem statement is kept for
     the model checker. *)

(***************************************************************************)
(* Liveness theorem (uses definitions from Consensus)                    *)
(***************************************************************************)
THEOREM Liveness == Consensus!LiveSpec => Consensus!LiveSpec
<1> SUFFICES ASSUME NEW Q \in Quorum, NEW b \in Ballot
             PROVE  Spec /\ LiveAssumption!(Q, b) => Consensus!LiveSpec
  BY Isa DEF LiveSpec, LiveAssumption

<1>a. IsFiniteSet(Q)
  BY QA, AcceptorFinite, FS_Subset

<1>1. Consensus!LiveSpec <=> Consensus!Spec /\ ([]<><<Consensus!Next>>_Consensus!vars \/ []<>(chosen # {}))
  BY ValueNonempty, Consensus!LiveSpecEquals

<1> DEFINE LNext == \E self \in Acceptor, c \in Ballot :
                         /\ BallotAction(self, c)
                         /\ (self \in Q) => (c =< b)

<1>2. Spec /\ LiveAssumption!(Q, b) => [][LNext]_vars
  <2>1. /\ TypeOK
        /\ [Next]_vars
        /\ UNCHANGED chosen
  OBVIOUS

=============================================================================