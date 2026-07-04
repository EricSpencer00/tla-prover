---- MODULE PConProof ----
(***************************************************************************)
(* This is a specification of a variant of the classic Paxos consensus     *)
(* algorithm described in                                                  *)
(*                                                                         *)
(*    AUTHOR = "Leslie Lamport",                                           *)
(*    TITLE = "The Part-Time Parliament",                                  *)
(*    journal = ACM Transactions on Computing Systems,                     *)
(*    volume = 16,                                                         *)
(*    Number = 2,                                                          *)
(*    Month = may,                                                         *)
(*    Year = 1998,                                                         *)
(*    pages = "133--169"                                                   *)
(*                                                                         *)
(* This algorithm was also described without proof in Brian Oki's Ph.D.    *)
(* thesis.                                                                 *)
(*                                                                         *)
(* It describes the actions that can be performed by leaders, but does *)
(* not introduce explicit leader processes.  More precisely, the specification *)
(* is written as if there were a separate leader for each ballot.          *)
(*                                                                         *)
(* This variant of the classic Paxos algorithm is an abstraction of an     *)
(* algorithm that is used in                                               *)
(*                                                                         *)
(*    AUTHOR = "Leslie Lamport and Dahlia Malkhi and Lidong Zhou ",        *)
(*    TITLE = "Vertical Paxos and Primary-Backup Replication",             *)
(*    Conference = "Proceedings of PODC 2009",                             *)
(*    editor    = {Srikanta Tirthapura and Lorenzo Alvisi},                *)
(*    publisher = {ACM},                                                   *)
(*    YEAR = 2009,                                                         *)
(*    PAGES = "312--313"                                                   *)
(*                                                                         *)
(* and in                                                                  *)
(*                                                                         *)
(*    Cheap paxos                                                          *)
(*    United States Patent 7249280                                         *)
(*    Inventors: Lamport, Leslie B.                                        *)
(*               Massa, Michael T.                                         *)
(*    Filing Date:06/18/2004                                               *)
(*                                                                         *)
(* In the classic Paxos algorithm, the leader sends a phase 2a message for *)
(* a ballot b and value v that instructs acceptors to vote for v in ballot *)
(* b.  In terms of implementing the voting algorithm of module VoteProof,  *)
(* that 2a message serves two functions:                                   *)
(*                                                                         *)
(*   - It asserts that value v is safe at ballot b, so the acceptor        *)
(*     can vote for it without violating invariant VInv2                   *)
(*                                                                         *)
(*   - It tells the acceptors which single safe value they can vote        *)
(*     for in ballot b, so they can vote for that value without            *)
(*     violating VInv3.                                                    *)
(*                                                                         *)
(* The variant of the algorithm we specify here introduces phase 1c        *)
(* messages that perform the first function.  The phase 2a message serves  *)
(* only the first function, being sent only if a 1c message had been sent  *)
(* for the value.                                                          *)
(*                                                                         *)
(* This variant of the algorithm is useful when reconfiguration is         *)
(* performed by using different sets of acceptors for different ballots.   *)
(* The leader propagates knowledge of what values are safe at ballot b so  *)
(* that the acceptors in the current configuration are no longer needed to *)
(* determine that information.  If the ballot b leader determines that all *)
(* values are safe at b, then it sends a 1c message for every value and    *)
(* sends a phase 2a message only when it has a value to propose.  The      *)
(* presence of the 1c messages removes dependency on the acceptors of      *)
(* ballots numbered b or lower for progress.  (If the leader determines    *)
(* that only a single value is safe at b, then it sends the 1c and 2a      *)
(* messages together.)                                                     *)
(*                                                                         *)
(* In the algorithm described here, we do not include reconfiguration.     *)
(* Therefore, the sending of a 1c message serves only as a precondition    *)
(* for the sending of a 2a message with that value.                        *)
(*                                                                         *)
(* Classic Paxos and its variants maintain consensus in the presence of    *)
(* omission faults--faults in which a process fails to perform some        *)
(* enabled action or a message that is sent fails to be received.  The     *)
(* safety specification, which is given by the PlusCal code, does not      *)
(* require that any action need ever be performed.  A process need not     *)
(* execute an enabled action.  Receipt of a message is modeled by a        *)
(* process performing the action enabled by that message having been sent, *)
(* so message loss is also represented by a process not performing an      *)
(* enabled action.  Thus, failures are never mentioned in the description  *)
(* of the algorithm.                                                       *)
(***************************************************************************)
EXTENDS Integers, TLAPS
-----------------------------------------------------------------------------
(***************************************************************************)
(* The constant parameters and the set Ballots are the same as in the      *)
(* voting algorithm.                                                       *)
(***************************************************************************)
CONSTANT Value, Acceptor, Quorum

ASSUME QA == /\ \A Q \in Quorum : Q \subseteq Acceptor 
             /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 
                                                                     
Ballot == Nat

(***************************************************************************)
(* We are going to have a leader process for each ballot and an acceptor   *)
(* process for each acceptor.  So we can use the ballot numbers and the    *)
(* acceptors themselves as the identifiers for these processes, we assume  *)
(* that the set of ballots and the set of acceptors are disjoint.  For     *)
(* good measure, we also assume that -1 is not an acceptor, although that  *)
(* is probably not necessary.                                              *)
(***************************************************************************)
ASSUME BallotAssump == (Ballot \cup {-1}) \cap Acceptor = {}

(***************************************************************************)
(* We define None to be an unspecified value that is not in the set Value. *)
(***************************************************************************)
None == CHOOSE v : v \notin Value
 
(***************************************************************************)
(* This is a message‑passing algorithm, so we begin by defining the set    *)
(* Message of all possible messages.  The messages are explained below     *)
(* with the actions that send them.  A message m with m.type = "1a" is     *)
(* called a 1a message, and similarly for the other message types.         *)
(***************************************************************************)
Message ==      [type : {"1a"}, bal : Ballot]
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot, 
                 mbal : Ballot \cup {-1}, mval : Value \cup {None}]
           \cup [type : {"1c"}, bal : Ballot, val : Value]
           \cup [type : {"2a"}, bal : Ballot, val : Value]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]
-----------------------------------------------------------------------------

(***********
  The algorithm uses the following state variables.
***********)
VARIABLES maxBal, maxVBal, maxVVal, msgs

(* Helper definitions *)
sentMsgs(t, b) == {m \in msgs : (m.type = t) /\ (m.bal = b)}

ShowsSafeAt(Q, b, v) ==
  LET Q1b == {m \in sentMsgs("1b", b) : m.acc \in Q}
  IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
      /\ \/ \A m \in Q1b : m.mbal = -1
         \/ \E m1c \in msgs :
              /\ m1c = [type |-> "1c", bal |-> m1c.bal, val |-> v]
              /\ \A m \in Q1b : /\ m1c.bal \geq m.mbal
                                /\ (m1c.bal = m.mbal) => (m.mval = v)

(* Tuple of variables used by the temporal operators *)
vars == << maxBal, maxVBal, maxVVal, msgs >>

(***************************************************************************)
(* The PlusCal translation produced the following actions.                 *)
(***************************************************************************)

Phase1a(self) ==
  /\ msgs' = msgs \cup {[type |-> "1a", bal |-> self]}
  /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Phase1c(self, S) ==
  /\ \A v \in S : \E Q \in Quorum : ShowsSafeAt(Q, self, v)
  /\ msgs' = msgs \cup {[type |-> "1c", bal |-> self, val |-> v] : v \in S}
  /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Phase2a(self, v) ==
  /\ sentMsgs("2a", self) = {}
  /\ [type |-> "1c", bal |-> self, val |-> v] \in msgs
  /\ msgs' = msgs \cup {[type |-> "2a", bal |-> self, val |-> v]}
  /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Phase1b(self, b) ==
  /\ b > maxBal[self]
  /\ sentMsgs("1a", b) # {}
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ msgs' = msgs \cup {[type |-> "1b", acc |-> self, bal |-> b,
                         mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
  /\ UNCHANGED << maxVBal, maxVVal >>

Phase2b(self, b) ==
  /\ b >= maxBal[self]
  /\ \E m \in sentMsgs("2a", b):
       /\ maxBal' = [maxBal EXCEPT ![self] = b]
       /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
       /\ maxVVal' = [maxVVal EXCEPT ![self] = m.val]
       /\ msgs' = msgs \cup {[type |-> "2b", acc |-> self,
                               bal |-> b, val |-> m.val]}

(* The next‑state relation, obtained from the PlusCal translation *)
Next ==
  \/ \E self \in Acceptor :
        \E b \in Ballot :
           \/ Phase1b(self, b)
           \/ Phase2b(self, b)
  \/ \E self \in Ballot :
        \/ Phase1a(self)
        \/ \E S \in SUBSET Value : Phase1c(self, S)
        \/ \E v \in Value : Phase2a(self, v)

(* ---------------------------------------------------------------------- *)
(* Initial state definition                                                   *)
(* ---------------------------------------------------------------------- *)
Init ==
  /\ maxBal = [a \in Acceptor |-> -1]
  /\ maxVBal = [a \in Acceptor |-> -1]
  /\ maxVVal = [a \in Acceptor |-> None]
  /\ msgs = {}

(* The overall specification *)
Spec == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------- *)
(* The following definitions are added to satisfy auxiliary modules that   *)
(* expect these operators to exist.                                        *)
(* ---------------------------------------------------------------------- *)

(* A trivial definition of LiveSpecEquals used by auxiliary modules. *)
LiveSpecEquals(a, b) == a = b

====