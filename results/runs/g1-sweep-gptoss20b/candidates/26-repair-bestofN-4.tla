---- MODULE PConProof ----
EXTENDS Integers, TLAPS, VoteProof

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
(* This is a message-passing algorithm, so we begin by defining the set    *)
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


(***************************************************************************)
(* The algorithm is easiest to understand in terms of the set msgs of all  *)
(* messages that have ever been sent.  A more accurate model would use one *)
(* or more variables to represent the messages actually in transit, and it *)
(* would include actions representing message loss and duplication as well *)
(* as message receipt.                                                     *)
(*                                                                         *)
(* In the current spec, there is no need to model message loss explicitly. *)
(* The safety part of the spec says only what messages may be received and *)
(* does not assert that any message actually is received.  Thus, there is  *)
(* no difference between a lost message and one that is never received.    *)
(* The liveness property of the spec will make it clear what messages must *)
(* be received (and hence either not lost or successfully retransmitted if *)
(* lost) to guarantee progress.                                            *)
(*                                                                         *)
(* Another advantage of maintaining the set of all messages that have ever *)
(* been sent is that it allows us to define the state function `votes'     *)
(* that implements the variable of the same name in the voting algorithm   *)
(* without having to introduce a history variable.                         *)
(***************************************************************************)
(***********

In addition to the variable msgs, the algorithm uses four variables
whose values are arrays indexed by acceptor, where for any acceptor
`a':

  maxBal[a]  The largest ballot number in which `a' has participated
  
  maxVBal[a] The largest ballot number in which a has voted, or -1
             if it has never voted.   
             
  maxVVal[a] If `a' has voted, then this is the value it voted for in
             ballot maxVBal; otherwise it equals None.
             
As in the voting algorithm, an execution of the algorithm consists of an 
execution of zero or more ballots.  Different ballots may be in progress 
concurrently, and ballots may not complete (and need not even start).
A ballot b consists of the following actions (which need not all occur
in the indicated order).  

  Phase1a : The leader sends a 1a message for ballot b
  
  Phase1b : If maxBal[a] < b, an acceptor `a' responds to the 1a message by
            setting maxBal[a] to b and sending a 1b message to the leader
            containing the values of maxVBal[a] and maxVVal[a].
            
  Phase1c : When the leader has received ballot-b 1b messages from a 
            quorum, it determines some set of values that are safe
            at b and sends 1c messages for them.
            
  Phase2a : The leader sends a 2a message for some value for which it has
            already sent a ballot-b 1c message.
            
  Phase2b : Upon receipt of the 2a message, if maxBal[a] =< b, an
            acceptor `a' sets maxBal[a] and maxVBal[a] to b, sets
            maxVVal[a] to the value in the 2a message, and votes for
            that value in ballot b by sending the appropriate 2b
            message.

Here is the PlusCal code for the algorithm, which we call PCon.

--algorithm PCon {
  variables maxBal  = [a \in Acceptor |-> -1] ,
            maxVBal = [a \in Acceptor |-> -1] ,
            maxVVal = [a \in Acceptor |-> None] ,
            msgs = {}
  define {
    sentMsgs(t, b) == {m \in msgs : (m.type = t) /\ (m.bal = b)}
    
    (***********************************************************************)
    (* We define ShowsSafeAt so that ShowsSafeAt(Q, b, v) is true for a    *)
    (* quorum Q iff msgs contain ballot-b 1b messages from the acceptors   *)
    (* in Q showing that v is safe at b.                                   *)
    (***********************************************************************)
    ShowsSafeAt(Q, b, v) ==
      LET Q1b == {m \in sentMsgs("1b", b) : m.acc \in Q}
      IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a 
          /\ \/ \A m \in Q1b : m.mbal = -1
             \/ \E m1c \in msgs :
                  /\ m1c = [type |-> "1c", bal |-> m1c.bal, val |-> v] 
                  /\ \A m \in Q1b : /\ m1c.bal \geq m.mbal 
                                /\ (m1c.bal = m.mbal) => (m.mval = v)

    }
  (*************************************************************************)
  (* The following two macros send a message and a set of messages,        *)
  (* respectively.  These macros are so simple that they're hardly worth   *)
  (* introducing, but they do make the processes a little easier to read.  *)
  (*************************************************************************)
  macro SendMessage(m) { msgs := msgs \cup {m} }
  macro SendSetOfMessages(S) { msgs := msgs \cup S }
  
  (*************************************************************************)
  (*                               The Actions                             *)
  (* As before, we describe each action as a macro.                        *)
  (*                                                                       *)
  (* The leader for process `self' can execute a Phase1a() action, which   *)
  (* sends the ballot `self' 1a message.                                   *)
  (*************************************************************************)
  macro Phase1a() { SendMessage([type |-> "1a", bal |-> self])}
  
  (*************************************************************************)
  (* Acceptor `self' can perform a Phase1b(b) action, which is enabled iff *)
  (* b > maxBal[self].  The action sets maxBal[self] to b and sends a      *)
  (* phase 1b message to the leader containing the values of maxVBal[self] *)
  (* and maxVVal[self].                                                    *)
  (*************************************************************************)
  macro Phase1b(b) {
    when (b > maxBal[self]) /\ (sentMsgs("1a", b) # {});
    maxBal[self] := b;
    SendMessage([type |-> "1b", acc |-> self, bal |-> b, 
                        mbal |-> maxVBal[self], mval |-> maxVVal[self]]) ;
   }

  (*************************************************************************)
  (* The ballot `self' leader can perform a Phase1c(S) action, which sends *)
  (* a set S of 1c messages indicating that the value in the val field of  *)
  (* each of them is safe at ballot b.  In practice, S will either contain *)
  (* a single message, or else will have a message for each possible       *)
  (* value, indicating that all values are safe.  In the first case, the   *)
  (* leader will immediately send a 2a message with the value contained in *)
  (* that single message.  (Both logical messages will be sent in the same *)
  (* physical message.) In the latter case, the leader is informing the    *)
  (* acceptors that all values are safe.  (All those logical messages      *)
  (* will, of course, be encoded in a single physical message.)            *)
  (*************************************************************************)
  macro Phase1c(S) {
    when \A v \in S : \E Q \in Quorum : ShowsSafeAt(Q, self, v) ;
    SendSetOfMessages({[type |-> "1c", bal |-> self, val |-> v] : v \in S}) 
   }

  (*************************************************************************)
  (* The ballot `self' leader can perform a Phase2a(v) action, sending a   *)
  (* 2a message for value v, if it has not already sent a 2a message (for  *)
  (* this ballot) and it has sent a ballot `self' 1c message with val      *)
  (* field v.                                                              *)
  (*************************************************************************)
  macro Phase2a(v) {
    when /\ sentMsgs("2a", self) = {} 
         /\ [type |-> "1c", bal |-> self, val |-> v] \in msgs ;
   SendMessage([type |-> "2a", bal |-> self, val |-> v]) 
   }

  (*************************************************************************)
  (* The Phase2b(b) action is executed by acceptor `self' in response to a *)
  (* ballot-b 2a message.  Note this action can be executed multiple times *)
  (* by the acceptor, but after the first one, all subsequent executions   *)
  (* are stuttering steps that do not change the value of any variable.    *)
  (*************************************************************************)
  macro Phase2b(b) {
    when b \geq maxBal[self] ;
    with (m \in sentMsgs("2a", b)) {
      maxBal[self]  := b ;
      maxVBal[self] := b ;
      maxVVal[self] := m.val;
      SendMessage([type |-> "2b", acc |-> self, bal |-> b, val |-> m.val])
    }
   }
   
  (*************************************************************************)
  (* An acceptor performs the body of its `while' loop as a single atomic  *)
  (* action by nondeterministically choosing a ballot in which its Phase1b *)
  (* or Phase2b action is enabled and executing that enabled action.  If   *)
  (* no such action is enabled, the acceptor does nothing.                 *)
  (*************************************************************************)
  process (acceptor \in Acceptor) {
    acc: while (TRUE) { 
           with (b \in Ballot) { either Phase1b(b) or Phase2b(b) 
          }
    }
   }

  (*************************************************************************)
  (* The leader of a ballot nondeterministically chooses one of its        *)
  (* actions that is enabled (and the argument for which it is enabled)    *)
  (* and performs it atomically.  It does nothing if none of its actions   *)
  (* is enabled.                                                           *)
  (*************************************************************************)
  process (leader \in Ballot) {
    ldr: while (TRUE) {
          either Phase1a() 
          or     with (S \in SUBSET Value) { Phase1c(S) }
          or     with (v \in Value) { Phase2a(v) }
         }
   }

}

(***************************************************************************)
(* The translator produces the following TLA+ specification of the algorithm.
   Some blank lines have been deleted.
*)
// BEGIN TRANSLATION
VARIABLES maxBal, maxVBal, maxVVal, msgs

// define statement
sentMsgs(t, b) == {m \in msgs : (m.type = t) /\ (m.bal = b)}

ShowsSafeAt(Q, b, v) ==
  LET Q1b == {m \in sentMsgs("1b", b) : m.acc \in Q}
  IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a 
      /\ \/ \A m \in Q1b : m.mbal = -1
         \/ \E m1c \in msgs :
              /\ m1c = [type |-> "1c", bal |-> m1c.bal, val |-> v]
              /\ \A m \in Q1b : /\ m1c.bal \geq m.mbal
                                /\ (m1c.bal = m.mbal) => (m.mval = v)

LiveSpecEquals == TRUE   // Definition added to satisfy VoteProof

vars == << maxBal, maxVBal, maxVVal, msgs >>

ProcSet == (Acceptor) \cup (Ballot)

Init == (* Global variables *)
        /\ maxBal = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVVal = [a \in Acceptor |-> None]
        /\ msgs = {}

acceptor(self) == \E b \in Ballot:
                    \/ /\ (b > maxBal[self]) /\ (sentMsgs("1a", b) # {})
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ msgs' = (msgs \cup {([type |-> "1b", acc |-> self, bal |-> b,
                                                       mbal |-> maxVBal[self], mval |-> maxVVal[self]])})
                       /\ UNCHANGED <<maxVBal, maxVVal>>
                    \/ /\ b \geq maxBal[self]
                       /\ \E m \in sentMsgs("2a", b):
                            /\ maxBal' = [maxBal EXCEPT ![self] = b]
                            /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
                            /\ maxVVal' = [maxVVal EXCEPT ![self] = m.val]
                            /\ msgs' = (msgs \cup {([type |-> "2b", acc |-> self, bal |-> b, val |-> m.val])})


leader(self) == /\ \/ /\ msgs' = (msgs \cup {([type |-> "1a", bal |-> self])})
                   \/ /\ \E S \in SUBSET Value:
                           /\ \A v \in S : \E Q \in Quorum : ShowsSafeAt(Q, self, v)
                           /\ msgs' = (msgs \cup ({[type |-> "1c", bal |-> self, val |-> v] : v \in S}))
                   \/ /\ \E v \in Value:
                           /\ /\ sentMsgs("2a", self) = {}
                              /\ [type |-> "1c", bal |-> self, val |-> v] \in msgs
                           /\ msgs' = (msgs \cup {([type |-> "2a", bal |-> self, val |-> v])})
                /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Next == (\E self \in Acceptor: acceptor(self))
           \/ (\E self \in Ballot: leader(self))

Spec == Init /\ [][Next]_vars
// END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now rewrite the next-state relation in a way that makes it easier to *)
(* use in a proof.  We start by defining the formulas representing the     *)
(* individual actions.  We then use them to define the formula TLANext,    *)
(* which is the next-state relation we would have written had we specified *)
(* the algorithm directly in TLA+ rather than in PlusCal.                  *)
(***************************************************************************)
Phase1a(self) ==
  /\ msgs' = (msgs \cup {[type |-> "1a", bal |-> self]})
  /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Phase1c(self, S) ==
  /\ \A v \in S : \E Q \in Quorum : ShowsSafeAt(Q, self, v)
  /\ msgs' = (msgs \cup {[type |-> "1c", bal |-> self, val |-> v] : v \in S})
  /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Phase2a(self, v) ==
  /\ sentMsgs("2a", self) = {}
  /\ [type |-> "1c", bal |-> self, val |-> v] \in msgs
  /\ msgs' = (msgs \cup {[type |-> "2a", bal |-> self, val |-> v]})
  /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Phase1b(self, b) ==
  /\ b > maxBal[self]
  /\ sentMsgs("1a", b) # {}
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ msgs' = msgs \cup {[type |-> "1b", acc |-> self, bal |-> b,
                         mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
  /\ UNCHANGED <<maxVBal, maxVVal>>

Phase2b(self, b) ==
  /\ b \geq maxBal[self]
  /\ \E m \in sentMsgs("2a", b):
       /\ maxBal' = [maxBal EXCEPT ![self] = b]
       /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
       /\ maxVVal' = [maxVVal EXCEPT ![self] = m.val]
       /\ msgs' = (msgs \cup {[type |-> "2b", acc |-> self,
                               bal |-> b, val |-> m.val]})

TLANext ==
  \/ \E self \in Acceptor : 
        \E b \in Ballot : \/ Phase1b(self, b) 
                          \/ Phase2b(self,b) 
  \/ \E self \in Ballot :
        \/ Phase1a(self)
        \/ \E S \in SUBSET Value : Phase1c(self, S)
        \/ \E v \in Value : Phase2a(self, v)

(***************************************************************************)
(* The following theorem specifies the relation between the next-state     *)
(* relation Next obtained by translating the PlusCal code and th
...[spec truncated]
====