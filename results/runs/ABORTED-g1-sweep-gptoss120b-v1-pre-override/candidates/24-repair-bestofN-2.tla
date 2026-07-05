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

----------------------------------------------------------------------------
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
-----------------------------------------------------------------------------

(***************************************************************************)
(* We pretend that which acceptors are good and which are malicious is     *)
(* specified in advance.  Of course, the algorithm executed by the good    *)
(* acceptors makes no use of which acceptors are which.  Hence, we can     *)
(* think of the sets of good and malicious acceptors as "prophecy          *)
(* constants" that are used only for showing that the algorithm implements *)
(* the PCon algorithm.                                                     *)
(*                                                                         *)
(* We can assume that a maximal set of acceptors are bad, since a bad      *)
(* acceptor is allowed to do anything--including acting like a good one.   *)
(*                                                                         *)
(* The basic idea is that the good acceptors try to execute the Paxos      *)
(* consensus algorithm, while the bad acceptors may try to prevent them.   *)
(*                                                                         *)
(* We do not distinguish between faulty and non-faulty leaders.  Safety    *)
(* must be preserved even if all leaders are malicious, so we allow any    *)
(* leader to send any syntactically correct message at any time.  (In an   *)
(* implementation, syntactically incorrect messages are simply ignored by  *)
(* non-faulty acceptors and have no effect.) Assumptions about leader      *)
(* behavior are required only for liveness.                                *)
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
(* The following are the assumptions about acceptors and quorums that are  *)
(* needed to ensure safety of our algorithm.                               *)
(***************************************************************************)
ASSUME BQA ==
          /\ Acceptor \cap FakeAcceptor = {}
          /\ \A Q \in ByzQuorum : Q \subseteq ByzAcceptor
          /\ \A Q1, Q2 \in ByzQuorum : Q1 \cap Q2 \cap Acceptor # {}
          /\ \A Q \in WeakQuorum : /\ Q \subseteq ByzAcceptor
                                   /\ Q \cap Acceptor # {}

(***************************************************************************)
(* The following assumption is not needed for safety, but it will be       *)
(* needed to ensure liveness.                                              *)
(***************************************************************************)
ASSUME BQLA ==
          /\ \E Q \in ByzQuorum : Q \subseteq Acceptor
          /\ \E Q \in WeakQuorum : Q \subseteq Acceptor
-----------------------------------------------------------------------------

(***************************************************************************)
(* We now define the set BMessage of all possible messages.                *)
(***************************************************************************)
1aMessage == [type : {"1a"},  bal : Ballot]

1bMessage ==
  [type : {"1b"}, bal : Ballot,
   mbal : Ballot \cup {-1}, mval : Value \cup {None},
   m2av : SUBSET [val : Value, bal : Ballot],
   acc : ByzAcceptor]

1cMessage ==
  [type : {"1c"}, bal : Ballot, val : Value]

2avMessage ==
   [type : {"2av"}, bal : Ballot, val : Value, acc : ByzAcceptor]

2bMessage == [type : {"2b"}, acc : ByzAcceptor, bal : Ballot, val : Value]

BMessage ==
  1aMessage \cup 1bMessage \cup 1cMessage \cup 2avMessage \cup 2bMessage

(***************************************************************************)
(* We will need the following simple fact about these sets of messages.    *)
(***************************************************************************)
LEMMA BMessageLemma ==
         \A m \in BMessage :
           /\ (m \in 1aMessage) <=>  (m.type = "1a")
           /\ (m \in 1bMessage) <=>  (m.type = "1b")
           /\ (m \in 1cMessage) <=>  (m.type = "1c")
           /\ (m \in 2avMessage) <=>  (m.type = "2av")
           /\ (m \in 2bMessage) <=>  (m.type = "2b")
<1>1. /\ \A m \in 1aMessage : m.type = "1a"
      /\ \A m \in 1bMessage : m.type = "1b"
      /\ \A m \in 1cMessage : m.type = "1c"
      /\ \A m \in 2avMessage : m.type = "2av"
      /\ \A m \in 2bMessage : m.type = "2b"
  BY DEF 1aMessage, 1bMessage, 1cMessage, 2avMessage, 2bMessage
<1>2. QED
  BY <1>1 DEF BMessage
-----------------------------------------------------------------------------

(****************************************************************************
We now give the algorithm.  The basic idea is that the set Acceptor of
real acceptors emulate an execution of the PCon algorithm with
Acceptor as its set of acceptors.  Of course, they must do that
without knowing which of the other processes in ByzAcceptor are real
acceptors and which are fake acceptors.  In addition, they don't know
whether a leader is behaving according to the PCon algorithm or if it
is malicious.

The main idea of the algorithm is that, before performing an action of
the PCon algorithm, a good acceptor determines that this action is
actually enabled in that algorithm.  Since an action is enabled by the
receipt of one or more messages, the acceptor has to determine that
the enabling messages are legal PCon messages.  Because algorithm PCon
allows a 1a message to be sent at any time, the only acceptor action
whose enabling messages must be checked is the Phase2b action.  It is
enabled iff the appropriate 1c message and 2a message are legal.  The
1c message is legal iff the leader has received the necessary 1b
messages.  The acceptor therefore maintains a set of 1b messages that
it knows have been sent, and checks that those 1b messages enable the
sending of the 1c message.

A 2a message is legal in the PCon algorithm iff (i) the corresponding
1c message is legal and (ii) it is the only 2a message that the leader
sends.  In the BPCon algorithm, there are no explicit 2a messages.
They are implicitly sent by the acceptors when they send enough 2av
messages.

We leave unspecified how an acceptor discovers what 1b messages have
been sent.  In the Castro-Liskov algorithm, this is done by having
acceptors relay messages sent by other acceptors.  An acceptor knows
that a 1b message has been sent if it receives it directly or else
receives a copy from a weak Byzantine quorum of acceptors.  A
(non-malicious) leader must determine what 1b messages acceptors know
about so it chooses a value so that a quorum of acceptors will act on
its Phase1c message and cause that value to be chosen.  However, this
is necessary only for liveness, so we ignore this for now.

In other implementations of our algorithm, the leader sends along with
the 1c message a proof that the necessary 1b messages have been sent.
The easiest way to do this is to have acceptors digitally sign their 1b
messages, so a copy of the message proves that it has been sent (by the
acceptor indicated in the message's acc field).  The necessary proofs
can also be constructed using only message authenticators (like the
ones used in the Castro-Liskov algorithm); how this is done is
described elsewhere.

In the abstract algorithm presented here, which we call
BPCon, we do not specify how acceptors learn what 1b
messages have been sent.  We simply introduce a variable knowsSent such
that knowsSent[a] represents the set of 1b messages that (good)
acceptor a knows have been sent, and have an action that
nondeterministically adds sent 1b messages to this set.

--algorithm BPCon {
  (**************************************************************************
The variables:

    maxBal[a]  = Highest ballot in which acceptor a has participated.

    maxVBal[a] = Highest ballot in which acceptor a has cast a vote
                 (sent a 2b message); or -1 if it hasn't cast a vote.

    maxVVal[a] = Value acceptor a has voted for in ballot maxVBal[a],
                  or None if maxVBal[a] = -1.

    2avSent[a] = A set of records in [val : Value, bal : Ballot]
                 describing the 2av messages that a has sent.  A
                 record is added to this set, and any element with
                 the same val field (and lower bal field) removed
                 when a sends a 2av message.

    knownSent[a] = The set of 1b messages that acceptor a knows have
                   been sent.

    bmsgs = The set of all messages that have been sent.  See the
            discussion of the msgs variable in module PConProof
            to understand our modeling of message passing.
  **************************************************************************)
  variables maxBal  = [a \in Acceptor |-> -1],
            maxVBal = [a \in Acceptor |-> -1] ,
            maxVVal = [a \in Acceptor |-> None] ,
            2avSent = [a \in Acceptor |-> {}],
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
   SendMessage([type |-> "1b", bal |-> b, acc |-> self, m2av |-> 2avSent[self],
                mbal |-> maxVBal[self], mval |-> maxVVal[self]])
   }

  macro Phase1c() {
    with (S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]) {
      SendSetOfMessages(S) }
   }

  macro Phase2av(b) {
    when /\ maxBal[self] =< b
         /\ \A r \in 2avSent[self] : r.bal < b ;
    with (m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}) {
       SendMessage([type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]) ;
       2avSent[self] :=  {r \in 2avSent[self] : r.val # m.val}
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
    with ( m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage :
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

=============================================================================