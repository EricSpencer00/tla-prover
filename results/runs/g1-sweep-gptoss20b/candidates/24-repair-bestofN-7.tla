---- MODULE BPConProof ----
EXTENDS Integers, FiniteSets, FiniteSetTheorems, TLAPS

CONSTANT Value

Ballot == Nat

None == CHOOSE v : v \notin Value

CONSTANTS Acceptor,
          FakeAcceptor,
          ByzQuorum,
          WeakQuorum

ByzAcceptor == Acceptor \cup FakeAcceptor

ASSUME BallotAssump == (Ballot \cup {-1}) \cap ByzAcceptor = {}

ASSUME BQA ==
          /\ Acceptor \cap FakeAcceptor = {}
          /\ \A Q \in ByzQuorum : Q \subseteq ByzAcceptor
          /\ \A Q1, Q2 \in ByzQuorum : Q1 \cap Q2 \cap Acceptor # {}
          /\ \A Q \in WeakQuorum : /\ Q \subseteq ByzAcceptor
                                   /\ Q \cap Acceptor # {}

ASSUME BQLA ==
          /\ \E Q \in ByzQuorum : Q \subseteq Acceptor
          /\ \E Q \in WeakQuorum : Q \subseteq Acceptor

1aMessage == [type : {"1a"}, bal : Ballot]
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

LEMMA BMessageLemma ==
   \A m \in BMessage :
     /\ (m \in 1aMessage) <=>  (m.type = "1a")
     /\ (m \in 1bMessage) <=>  (m.type = "1b")
     /\ (m \in 1cMessage) <=>  (m.type = "1c")
     /\ (m \in 2avMessage) <=>  (m.type = "2av")
     /\ (m \in 2bMessage) <=>  (m.type = "2b")

variables maxBa, maxVB, maxVV, sent2av, knowsSent, bmsgs

DEFINE
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

macro SendMessage(m) { bmsgs := bmsgs \cup {m} }
macro SendSetOfMessages(S) { bmsgs := bmsgs \cup S }

macro Phase1a() { SendMessage([type |-> "1a", bal |-> self]) }

macro Phase1b(b) {
   when (b > maxBa[self]) /\ (sentMsgs("1a", b) # {})
   /\ maxBa[self] := b
   /\ SendMessage([type |-> "1b", bal |-> b, acc |-> self, m2av |-> sent2av[self],
                   mbal |-> maxVB[self], mval |-> maxVV[self]])
}

macro Phase1c() {
   with (S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]) {
     SendSetOfMessages(S) }
}

macro Phase2av(b) {
   when /\ maxBa[self] =< b
        /\ \A r \in sent2av[self] : r.bal < b
   with (m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}) {
      SendMessage([type |-> "2av", bal |-> b, val |-> m.val, acc |-> self])
      /\ sent2av[self] := {r \in sent2av[self] : r.val # m.val}
                           \cup {[val |-> m.val, bal |-> b]} }
   /\ maxBa[self]  := b
}

macro Phase2b(b) {
   when maxBa[self] =< b
   with (v \in {vv \in Value :
                 \E Q \in ByzQuorum :
                    \A aa \in Q :
                       \E m \in sentMsgs("2av", b) : /\ m.val = vv
                                                     /\ m.acc = aa} ) {
     SendMessage([type |-> "2b", acc |-> self, bal |-> b, val |-> v])
     /\ maxVV[self] := v }
   /\ maxBa[self] := b
   /\ maxVB[self] := b
}

macro LearnsSent(b) {
   with (S \in SUBSET sentMsgs("1b", b)) {
     knowsSent[self] := knowsSent[self] \cup S }
}

macro FakingAcceptor() {
   with ( m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage :
                    mm.acc = self} ) {
      SendMessage(m) }
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

====