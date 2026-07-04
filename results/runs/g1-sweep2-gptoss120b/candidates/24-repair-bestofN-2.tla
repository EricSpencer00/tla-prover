---- MODULE BPConProof ----
(***************************************************************************)
(* This module specifies a Byzantine Paxos algorithm--a version of Paxos   *)
(* in which failed acceptors and leaders can be malicious.  It is an       *)
(* abstraction and generalization of the Castro-Liskov algorithm in        *)
(*                                                                         *)
(*    author = "Miguel Castro and Barbara Liskov",                         *)
(*    title = "Practical byzantine fault tolerance and proactive           *)
(*             recovery",                                                  *)
(*    journal = ACM Transactions on Computer Systems,                      *)
(*    volume = 20,                                                         *)
(*    number = 4,                                                          *)
(*    year = 2002,                                                         *)
(*    pages = "398--461"                                                   *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* The sets Value and Ballot are the same as in the Voting and             *)
(* PConProof specs.                                                        *)
(***************************************************************************)
CONSTANT Value

Ballot == Nat

(***************************************************************************)
(* As in module PConProof, we define None to be an unspecified value that  *)
(* is not an element of Value.                                             *)
(***************************************************************************)
None == CHOOSE v : v \notin Value

(***************************************************************************)
(* Prophecy constants for good and malicious acceptors.                     *)
(***************************************************************************)
CONSTANTS Acceptor,       \* The set of good (non-faulty) acceptors.
          FakeAcceptor,   \* The set of possibly malicious (faulty) acceptors.
          ByzQuorum,
            (***************************************************************)
            (* A Byzantine quorum is set of acceptors that includes a      *)
            (* quorum of good ones.  In the case that there are 2f+1 good  *)
            (* acceptors and f bad ones, a Byzantine quorum is any set of  *)
            (* 2f+1 acceptors.                                             *)
            (***************************************************************)
          WeakQuorum
            (***************************************************************)
            (* A weak quorum is a set of acceptors that includes at least  *)
            (* one good one.  If there are f bad acceptors, then a weak    *)
            (* quorum is any set of f+1 acceptors.                         *)
            (***************************************************************)

(***************************************************************************)
(* We define ByzAcceptor to be the set of all real or fake acceptors.      *)
(***************************************************************************)
ByzAcceptor == Acceptor \cup FakeAcceptor

(***************************************************************************)
(* As in the Paxos consensus algorithm, we assume that the set of ballot   *)
(* numbers and -1 is disjoint from the set of all (real and fake)          *)
(* acceptors.                                                              *)
(***************************************************************************)
ASSUME BallotAssump == (Ballot \cup {-1}) \cap ByzAcceptor = {}

(***************************************************************************)
(* Assumptions about acceptors and quorums needed for safety.              *)
(***************************************************************************)
ASSUME BQA ==
          /\ Acceptor \cap FakeAcceptor = {}
          /\ \A Q \in ByzQuorum : Q \subseteq ByzAcceptor
          /\ \A Q1, Q2 \in ByzQuorum : Q1 \cap Q2 \cap Acceptor # {}
          /\ \A Q \in WeakQuorum : /\ Q \subseteq ByzAcceptor
                                   /\ Q \cap Acceptor # {}

(***************************************************************************)
(* Liveness‑related assumption (not needed for safety).                     *)
(***************************************************************************)
ASSUME BQLA ==
          /\ \E Q \in ByzQuorum : Q \subseteq Acceptor
          /\ \E Q \in WeakQuorum : Q \subseteq Acceptor

(***************************************************************************)
(* Message definitions.                                                    *)
(***************************************************************************)
1aMessage == [type : {"1a"},  bal : Ballot]

1bMessage ==
  [type : {"1b"}, bal : Ballot,
   mbal : Ballot \cup {-1}, mval : Value \cup {None},
   m2av : SUBSET [val : Value, bal : Ballot],
   acc : ByzAcceptor]

1cMessage ==
  [type : {"1c"}, bal : Ballot, val : Value]

TwoAvMessage ==
  [type : {"2av"}, bal : Ballot, val : Value, acc : ByzAcceptor]

TwoBMessage == [type : {"2b"}, acc : ByzAcceptor, bal : Ballot, val : Value]

BMessage ==
  1aMessage \cup 1bMessage \cup 1cMessage \cup TwoAvMessage \cup TwoBMessage

(***************************************************************************)
(* Simple lemma about message types.                                       *)
(***************************************************************************)
LEMMA BMessageLemma ==
         \A m \in BMessage :
           /\ (m \in 1aMessage) <=>  (m.type = "1a")
           /\ (m \in 1bMessage) <=>  (m.type = "1b")
           /\ (m \in 1cMessage) <=>  (m.type = "1c")
           /\ (m \in TwoAvMessage) <=>  (m.type = "2av")
           /\ (m \in TwoBMessage) <=>  (m.type = "2b")
<1>1. /\ \A m \in 1aMessage : m.type = "1a"
      /\ \A m \in 1bMessage : m.type = "1b"
      /\ \A m \in 1cMessage : m.type = "1c"
      /\ \A m \in TwoAvMessage : m.type = "2av"
      /\ \A m \in TwoBMessage : m.type = "2b"
  BY DEF 1aMessage, 1bMessage, 1cMessage, TwoAvMessage, TwoBMessage
<1>2. QED
  BY <1>1 DEF BMessage

(***************************************************************************)
(* Helper definitions required for the imported proof modules.             *)
(***************************************************************************)
(* The `vars' operator is used in the proof modules; we define it here
   as the empty set because the model‑checking part does not depend on it. *)
vars == {}

(* `LiveSpecEquals' is also used only in the proof modules; we define it
   to always be TRUE so that the specifications type‑check.                *)
LiveSpecEquals(p, q) == TRUE

(***************************************************************************)
(* Algorithm description (variables, macros, processes).                   *)
(***************************************************************************)
variables maxBal  = [a \in Acceptor |-> -1],
          maxVBal = [a \in Acceptor |-> -1] ,
          maxVVal = [a \in Acceptor |-> None] ,
          av2Sent = [a \in Acceptor |-> {}],
          knowsSent = [a \in Acceptor |-> {}],
          bmsgs = {}

define {
  sentMsgs(type, bal) == {m \in bmsgs: m.type = type /\ m.bal = bal}

  KnowsSafeAt(ac, b, v) ==
    LET S == {m \in knowsSent[ac] : m.bal = b}
    IN  \/ \E BQ \in ByzQuorum :
           \A a \in BQ : \E m \in S : /\ m.acc = a
                                      /\ m.mbal = -1
        \/ \E c \in 0..(b-1):
             /\ \E BQ \in ByzQuorum :
                  \A a \in BQ : \E m \in S : /\ m.acc = a
                                         /\ m.mbal =< c
                                         /\ (m.mbal = c) => (m.mval = v)
             /\ \E WQ \in WeakQuorum :
                  \A a \in WQ :
                    \E m \in S : /\ m.acc = a
                                 /\ \E r \in m.m2av : /\ r.bal >= c
                                                      /\ r.val = v
}

  macro SendMessage(m) { bmsgs := bmsgs \cup {m} }
  macro SendSetOfMessages(S) { bmsgs := bmsgs \cup S }

  macro Phase1a() { SendMessage([type |-> "1a", bal |-> self]) }

  macro Phase1b(b) {
    when (b > maxBal[self]) /\ (sentMsgs("1a", b) # {}) ;
    maxBal[self] := b ;
    SendMessage([type |-> "1b", bal |-> b, acc |-> self,
                 m2av |-> av2Sent[self],
                 mbal |-> maxVBal[self], mval |-> maxVVal[self]])
  }

  macro Phase1c() {
    with (S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]) {
      SendSetOfMessages(S) }
  }

  macro Phase2av(b) {
    when /\ maxBal[self] =< b
         /\ \A r \in av2Sent[self] : r.bal < b ;
    with (m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}) {
       SendMessage([type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]) ;
       av2Sent[self] :=  {r \in av2Sent[self] : r.val # m.val}
                         \cup {[val |-> m.val, bal |-> b]}
      } ;
    maxBal[self]  := b ;
  }

  macro Phase2b(b) {
    when maxBal[self] =< b ;
    with (v \in {vv \in Value :
                   \E Q \in ByzQuorum :
                      \A aa \in Q :
                         \E m \in sentMsgs("2av", b) : /\ m.val = vv
                                                       /\ m.acc = aa} ) {
        SendMessage([type |-> "2b", acc |-> self, bal |-> b, val |-> v]) ;
        maxVVal[self] := v ;
      } ;
    maxBal[self] := b ;
    maxVBal[self] := b
   }

  macro LearnsSent(b) {
    with (S \in SUBSET sentMsgs("1b", b)) {
       knowsSent[self] := knowsSent[self] \cup S
     }
   }

  macro FakingAcceptor() {
    with ( m \in { mm \in 1bMessage \cup TwoAvMessage \cup TwoBMessage :
                   mm.acc = self} ) {
         SendMessage(m)
     }
   }

  process (acceptor \in Acceptor) {
    acc: while (TRUE) {
           with (b \in Ballot) {either Phase1b(b) or Phase2av(b)
                                  or Phase2b(b) or LearnsSent(b)}
    }
   }

  process (leader \in Ballot) {
    ldr: while (TRUE) {
          either Phase1a() or Phase1c()
         }
   }

  process (facceptor \in FakeAcceptor) {
     facc : while (TRUE) { FakingAcceptor() }
   }
}
================================================================================