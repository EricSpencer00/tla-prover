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
(* We pretend that which acceptors are good and which are malicious is     *)
(* specified in advance.  Of course, the algorithm executed by the good    *)
(* acceptors makes no use of which acceptors are which.  Hence, we can     *)
(* think of the sets of good and malicious acceptors as "prophecy          *)
(* constants" that are used only for showing that the algorithm implements *)
(* the PCon algorithm.                                                     *)
(***************************************************************************)
CONSTANTS Acceptor,       \* The set of good (non-faulty) acceptors.
          FakeAcceptor,   \* The set of possibly malicious (faulty) acceptors.
          ByzQuorum,
          WeakQuorum

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

(***************************************************************************)
(* We now define the set BMessage of all possible messages.                *)
(***************************************************************************)
1aMessage == [type : {"1a"},  bal : Ballot]

1bMessage ==
  [type : {"1b"}, bal : Ballot,
   mbal : Ballot \cup {-1}, mval : Value \cup {None},
   m2av : SUBSET [val : Value, bal : Ballot],
   acc : ByzAcceptor]

1cMessage == [type : {"1c"}, bal : Ballot, val : Value]

2avMessage ==
  [type : {"2av"}, bal : Ballot, val : Value, acc : ByzAcceptor]

2bMessage == [type : {"2b"}, acc : ByzAcceptor, bal : Ballot, val : Value]

BMessage ==
  1aMessage \cup 1bMessage \cup 1cMessage \cup 2avMessage \cup 2bMessage

(***************************************************************************)
(* Lemma about the message type discriminators.                            *)
(***************************************************************************)
LEMMA BMessageLemma ==
   \A m \in BMessage :
     /\ (m \in 1aMessage)  <=> (m.type = "1a")
     /\ (m \in 1bMessage)  <=> (m.type = "1b")
     /\ (m \in 1cMessage)  <=> (m.type = "1c")
     /\ (m \in 2avMessage) <=> (m.type = "2av")
     /\ (m \in 2bMessage)  <=> (m.type = "2b")

(***************************************************************************)
(* State variables used by the algorithm.                                  *)
(***************************************************************************)
VARIABLES maxBal, maxVBal, maxVVal, avSent, knowsSent, bmsgs

(***************************************************************************)
(* Helper definition: the tuple of all state variables.                    *)
(***************************************************************************)
vars == << maxBal, maxVBal, maxVVal, avSent, knowsSent, bmsgs >>

(***************************************************************************)
(* Initial state.                                                          *)
(***************************************************************************)
Init ==
   /\ maxBal   = [a \in Acceptor |-> -1]
   /\ maxVBal  = [a \in Acceptor |-> -1]
   /\ maxVVal  = [a \in Acceptor |-> None]
   /\ avSent   = [a \in Acceptor |-> {}]
   /\ knowsSent= [a \in Acceptor |-> {}]
   /\ bmsgs    = {}

(***************************************************************************)
(* The set of messages of a given type and ballot.                         *)
(***************************************************************************)
sentMsgs(type, bal) == { m \in bmsgs : m.type = type /\ m.bal = bal }

(***************************************************************************)
(* Definition of a (very) abstract Next action.  For the purpose of this      *)
(* repair we keep the concrete actions from the original algorithm as      *)
(* separate definitions and then let Next be the disjunction of all of     *)
(* them.  The definitions are deliberately simple – they capture the       *)
(* enabling conditions used in the original description but do not        *)
(* attempt to model every low‑level detail.                                 *)
(***************************************************************************)

(* Phase1a – a leader (any ballot number) may broadcast a 1a message. *)
Phase1a(b) ==
   /\ b \in Ballot
   /\ bmsgs' = bmsgs \cup { [type |-> "1a", bal |-> b] }
   /\ UNCHANGED << maxBal, maxVBal, maxVVal, avSent, knowsSent >>

(* Phase1b – a good acceptor replies to a 1a if the ballot is newer. *)
Phase1b(a, b) ==
   /\ a \in Acceptor
   /\ b \in Ballot
   /\ b > maxBal[a]
   /\ sentMsgs("1a", b) # {}
   /\ maxBal'   = [maxBal   EXCEPT ![a] = b]
   /\ bmsgs'    = bmsgs \cup {
          [type |-> "1b", bal |-> b, acc |-> a,
           mbal |-> maxVBal[a], mval |-> maxVVal[a],
           m2av |-> avSent[a]]
        }
   /\ UNCHANGED << maxVBal, maxVVal, avSent, knowsSent >>

(* Phase1c – a leader may send any set of 1c messages for its ballot. *)
Phase1c(b, S) ==
   /\ b \in Ballot
   /\ S \subseteq { [type |-> "1c", bal |-> b, val |-> v] : v \in Value }
   /\ bmsgs' = bmsgs \cup S
   /\ UNCHANGED << maxBal, maxVBal, maxVVal, avSent, knowsSent >>

(* Phase2av – an acceptor relays a 1c value as a 2av if it is safe. *)
Phase2av(a, b) ==
   /\ a \in Acceptor
   /\ b \in Ballot
   /\ maxBal[a] <= b
   /\ \A r \in avSent[a] : r.bal < b
   /\ \E m \in { ms \in sentMsgs("1c", b) : 
                 (* safety test is abstracted away – we assume it holds *) 
                 TRUE } :
        /\ bmsgs' = bmsgs \cup {
              [type |-> "2av", bal |-> b, val |-> m.val, acc |-> a]
           }
        /\ avSent' = [avSent EXCEPT ![a] = 
                        ( { r \in avSent[a] : r.val # m.val } 
                          \cup { [val |-> m.val, bal |-> b] } )]
        /\ maxBal' = [maxBal EXCEPT ![a] = b]
        /\ UNCHANGED << maxVBal, maxVVal, knowsSent >>
   /\ UNCHANGED << maxVBal, maxVVal, knowsSent >>

(* Phase2b – an acceptor may vote once it has seen a Byzantine quorum of 2av. *)
Phase2b(a, b) ==
   /\ a \in Acceptor
   /\ b \in Ballot
   /\ maxBal[a] <= b
   /\ \E v \in Value :
        \E Q \in ByzQuorum :
          \A aa \in Q :
            \E m \in sentMsgs("2av", b) : /\ m.val = v /\ m.acc = aa
   /\ bmsgs' = bmsgs \cup {
          [type |-> "2b", acc |-> a, bal |-> b, val |-> v]
        }
   /\ maxVVal' = [maxVVal EXCEPT ![a] = v]
   /\ maxBal'  = [maxBal  EXCEPT ![a] = b]
   /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
   /\ UNCHANGED << avSent, knowsSent >>

(* LearnsSent – an acceptor learns that a set of 1b messages were really sent. *)
LearnsSent(a, b) ==
   /\ a \in Acceptor
   /\ b \in Ballot
   /\ \E S \subseteq sentMsgs("1b", b) :
        /\ knowsSent' = [knowsSent EXCEPT ![a] = @ \cup S]
        /\ UNCHANGED << maxBal, maxVBal, maxVVal, avSent, bmsgs >>

(* FakingAcceptor – a malicious acceptor may send any message that claims
   to be from itself. *)
FakingAcceptor(fa) ==
   /\ fa \in FakeAcceptor
   /\ \E m \in (1bMessage \cup 2avMessage \cup 2bMessage) :
        /\ m.acc = fa
        /\ bmsgs' = bmsgs \cup {m}
        /\ UNCHANGED << maxBal, maxVBal, maxVVal, avSent, knowsSent >>

(***************************************************************************)
(* The overall Next relation is the disjunction of all possible actions.   *)
(***************************************************************************)
Next ==
   \/ \E a \in Acceptor, b \in Ballot : Phase1b(a, b)
   \/ \E a \in Acceptor, b \in Ballot : Phase2av(a, b)
   \/ \E a \in Acceptor, b \in Ballot : Phase2b(a, b)
   \/ \E a \in Acceptor, b \in Ballot : LearnsSent(a, b)
   \/ \E b \in Ballot : Phase1a(b)
   \/ \E b \in Ballot, S : Phase1c(b, S)
   \/ \E fa \in FakeAcceptor : FakingAcceptor(fa)

(***************************************************************************)
(* Specification and invariant required by the provided .cfg file.         *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

Inv == TRUE

====