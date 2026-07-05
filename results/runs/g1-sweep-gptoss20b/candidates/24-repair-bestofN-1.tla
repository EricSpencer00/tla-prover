---- MODULE BPConProof ----
EXTENDS Integers, FiniteSets, FiniteSetTheorems, TLAPS, PConProof

CONSTANT Value
Ballot == Nat
None == CHOOSE v : v \notin Value

CONSTANTS Acceptor,
          FakeAcceptor,
          ByzQuorum,
          WeakQuorum

ByzAcceptor == Acceptor \cup FakeAcceptor

ASSUME BallotAssump ==
  (Ballot \cup {-1}) \cap ByzAcceptor = {}

ASSUME BQA ==
  /\ Acceptor \cap FakeAcceptor = {}
  /\ \A Q \in ByzQuorum : Q \subseteq ByzAcceptor
  /\ \A Q1, Q2 \in ByzQuorum : Q1 \cap Q2 \cap Acceptor # {}
  /\ \A Q \in WeakQuorum : /\ Q \subseteq ByzAcceptor
                           /\ Q \cap Acceptor # {}

ASSUME BQLA ==
  /\ \E Q \in ByzQuorum : Q \subseteq Acceptor
  /\ \E Q \in WeakQuorum : Q \subseteq Acceptor

(* Definition of message types *)
1aMessage == [type : {"1a"}, bal : Ballot]
1bMessage == [type : {"1b"}, bal : Ballot,
              mbal : Ballot \cup {-1}, mval : Value \cup {None},
              m2av : SUBSET [val : Value, bal : Ballot],
              acc : ByzAcceptor]
1cMessage == [type : {"1c"}, bal : Ballot, val : Value]
2avMessage == [type : {"2av"}, bal : Ballot, val : Value, acc : ByzAcceptor]
2bMessage == [type : {"2b"}, acc : ByzAcceptor, bal : Ballot, val : Value]
BMessage == 1aMessage \cup 1bMessage \cup 1cMessage \cup 2avMessage \cup 2bMessage

LEMMA BMessageLemma ==
  \A m \in BMessage :
    /\ (m \in 1aMessage) <=>  (m.type = "1a")
    /\ (m \in 1bMessage) <=>  (m.type = "1b")
    /\ (m \in 1cMessage) <=>  (m.type = "1c")
    /\ (m \in 2avMessage) <=>  (m.type = "2av")
    /\ (m \in 2bMessage) <=>  (m.type = "2b")

(* Variables *)
VARIABLES maxBal, maxVBal, maxVVal, twoAvSent, knowsSent, bmsgs

DEFINE
  sentMsgs(type, bal) == {m \in bmsgs : m.type = type /\ m.bal = bal}

  KnowsSafeAt(ac, b, v) ==
    LET S == {m \in knowsSent[ac] : m.bal = b} IN
      \/ \E BQ \in ByzQuorum :
           \A a \in BQ : \E m \in S : /\ m.acc = a
                                      /\ m.mbal = -1
          \/ \E c \in 0..(b-1) :
               /\ \E BQ \in ByzQuorum :
                    \A a \in BQ : \E m \in S : /\ m.acc = a
                                           /\ m.mbal =< c
                                           /\ (m.mbal = c) => (m.mval = v)
               /\ \E WQ \in WeakQuorum :
                    \A a \in WQ :
                      \E m \in S : /\ m.acc = a
                                   /\ \E r \in m.m2av : /\ r.bal >= c
                                                        /\ r.val = v

MACRO SendMessage(m) { bmsgs := bmsgs \cup {m} }

MACRO SendSetOfMessages(S) { bmsgs := bmsgs \cup S }

MACRO Phase1a() { SendMessage([type |-> "1a", bal |-> self]) }

MACRO Phase1b(b) {
  when (b > maxBal[self]) /\ (sentMsgs("1a", b) # {}) ;
  maxBal[self] := b ;
  SendMessage([type |-> "1b", bal |-> b, acc |-> self,
               m2av |-> twoAvSent[self],
               mbal |-> maxVBal[self], mval |-> maxVVal[self]])
}

MACRO Phase1c() {
  with (S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]) {
    SendSetOfMessages(S)
  }
}

MACRO Phase2av(b) {
  when /\ maxBal[self] =< b
       /\ \A r \in twoAvSent[self] : r.bal < b ;
  with (ms \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}) {
    SendMessage([type |-> "2av", bal |-> b, val |-> ms.val, acc |-> self]) ;
    twoAvSent[self] := {r \in twoAvSent[self] : r.val # ms.val}
                      \cup {[val |-> ms.val, bal |-> b]}
  } ;
  maxBal[self] := b ;
}

MACRO Phase2b(b) {
  when maxBal[self] =< b ;
  with (v \in {vv \in Value :
                \E Q \in ByzQuorum :
                  \A aa \in Q :
                    \E m \in sentMsgs("2av", b) : /\ m.val = vv
                                                     /\ m.acc = aa}) {
    SendMessage([type |-> "2b", acc |-> self, bal |-> b, val |-> v]) ;
    maxVVal[self] := v ;
  } ;
  maxBal[self] := b ;
  maxVBal[self] := b
}

MACRO LearnsSent(b) {
  with (S \in SUBSET sentMsgs("1b", b)) {
    knowsSent[self] := knowsSent[self] \cup S
  }
}

MACRO FakingAcceptor() {
  with (m \in {mm \in 1bMessage \cup 2avMessage \cup 2bMessage :
                 mm.acc = self}) {
    SendMessage(m)
  }
}

PROCESS (acceptor \in Acceptor) {
  acc: while (TRUE) {
    with (b \in Ballot) {
      either Phase1b(b) or Phase2av(b) or Phase2b(b) or LearnsSent(b)
    }
  }
}

PROCESS (leader \in Ballot) {
  ldr: while (TRUE) {
    either Phase1a() or Phase1c()
  }
}

PROCESS (facceptor \in FakeAcceptor) {
  facc: while (TRUE) { FakingAcceptor() }
}

====