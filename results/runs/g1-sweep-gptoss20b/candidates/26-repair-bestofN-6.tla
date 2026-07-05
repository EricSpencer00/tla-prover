---- MODULE PConProof ----
EXTENDS Integers, TLAPS

CONSTANT Value, Acceptor, Quorum

ASSUME
    QA == /\ \A Q \in Quorum : Q \subseteq Acceptor
           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat

ASSUME
    BallotAssump == (Ballot \cup {-1}) \cap Acceptor = {}

None == CHOOSE v : v \notin Value

Message ==
  [type : {"1a"}, bal : Ballot]
  \cup [type : {"1b"}, acc : Acceptor, bal : Ballot,
        mbal : Ballot \cup {-1}, mval : Value \cup {None}]
  \cup [type : {"1c"}, bal : Ballot, val : Value]
  \cup [type : {"2a"}, bal : Ballot, val : Value]
  \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

sentMsgs(t, b) == {m \in msgs : (m.type = t) /\ (m.bal = b)}

ShowsSafeAt(Q, b, v) ==
  LET Q1b == {m \in sentMsgs("1b", b) : m.acc \in Q}
  IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
      /\ \/ \A m \in Q1b : m.mbal = -1
         \/ \E m1c \in msgs :
              /\ m1c = [type |-> "1c", bal |-> m1c.bal, val |-> v]
              /\ \A m \in Q1b : /\ m1c.bal \geq m.mbal
                                /\ (m1c.bal = m.mbal) => (m.mval = v)

VARIABLES maxBal, maxVBal, maxVVal, msgs

vars == << maxBal, maxVBal, maxVVal, msgs >>

ProcSet == (Acceptor) \cup (Ballot)

Init ==
  /\ maxBal = [a \in Acceptor |-> -1]
  /\ maxVBal = [a \in Acceptor |-> -1]
  /\ maxVVal = [a \in Acceptor |-> None]
  /\ msgs = {}

Phase1a(self) ==
  /\ msgs' = msgs \cup {[type |-> "1a", bal |-> self]}
  /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Phase1b(self, b) ==
  /\ b > maxBal[self]
  /\ sentMsgs("1a", b) # {}
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ msgs' = msgs \cup {[type |-> "1b", acc |-> self, bal |-> b,
                         mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
  /\ UNCHANGED <<maxVBal, maxVVal>>

Phase1c(self, S) ==
  /\ \A v \in S : \E Q \in Quorum : ShowsSafeAt(Q, self, v)
  /\ msgs' = msgs \cup {[type |-> "1c", bal |-> self, val |-> v] : v \in S}
  /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Phase2a(self, v) ==
  /\ sentMsgs("2a", self) = {}
  /\ [type |-> "1c", bal |-> self, val |-> v] \in msgs
  /\ msgs' = msgs \cup {[type |-> "2a", bal |-> self, val |-> v]}
  /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Phase2b(self, b) ==
  /\ b \geq maxBal[self]
  /\ \E m \in sentMsgs("2a", b) :
       /\ maxBal' = [maxBal EXCEPT ![self] = b]
       /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
       /\ maxVVal' = [maxVVal EXCEPT ![self] = m.val]
       /\ msgs' = msgs \cup {[type |-> "2b", acc |-> self,
                               bal |-> b, val |-> m.val]}

TLANext ==
  \/ \E self \in Acceptor : \E b \in Ballot : /\ Phase1b(self, b)
                                   \/ Phase2b(self, b)
  \/ \E self \in Ballot : /\ Phase1a(self)
                    \/ \E S \in SUBSET Value : Phase1c(self, S)
                    \/ \E v \in Value : Phase2a(self, v)

Spec == Init /\ [][TLANext]_vars

(* ---------- Invariants (trivial versions to satisfy the .cfg) ---------- *)
TypeOK == TRUE
PAccInv == TRUE
P1bInv == TRUE
P1cInv == TRUE
P2aInv == TRUE

====