---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Account = a public key, which owns a chain of blocks (`accountChain`).
Account == PUBLICKEY
\* Every chain must start with its owner's open block (`accountBase`).
accountBase(k) == [account |-> k, ptype |-> "open", previd |-> NoHash, sender |-> NoHash, target |-> NoHash, amount |-> 0]
accountChain(k) == {accountBase(k)} \cup {b \in Hash : b.account = k /\ b.ptype # "open"}

RECURSIVE balanceOverChain(_, _)
balanceOverChain(k, S) ==
  IF S = {} THEN 0
  ELSE LET b == CHOOSE x \in S : TRUE IN
       (IF b.ptype = "send" THEN 0 ELSE b.amount) + balanceOverChain(k, S \ {b})

RECURSIVE sumBalances(_)
sumBalances(S) ==
  IF S = {} THEN 0
  ELSE LET k == CHOOSE x \in S : TRUE IN balanceOverChain(k, accountChain(k)) + sumBalances(S \ {k})

\* sentBlocks(k) = blocks in k's chain that moved coins to someone.
sentBlocks(k) == {b \in accountChain(k) : b.ptype = "send"}
RECURSIVE sentSum(_)
sentSum(S) ==
  IF S = {} THEN 0
  ELSE LET k == CHOOSE x \in S : TRUE IN
       (IF accountBase(k) \in S THEN 0 ELSE sentSum(sentBlocks(k))) + sentSum(S \ {k})

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Every node holds the same hash space, so the ledger is replicated identically.
NodeLedger(n) == [h \in Hash |-> ledger[h]]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [h \in Hash |-> [ptype |-> "empty", target |-> NoBlock]]
  /\ received = [n \in Node |-> {}]

Broadcast(b) ==
  /\ b \notin NodeLedger(\A n \in Node : n)
  /\ received' = [n \in Node |-> received[n] \cup {b}]
  /\ UNCHANGED <<lastHash, ledger>>

AddToLedger(n, h, b) ==
  /\ h \notin NodeLedger(n)
  /\ ledger' = [ledger EXCEPT ![h] = b]
  /\ UNCHANGED <<lastHash, received>>

ProcessBlock(n, b) == AddToLedger(n, b, b

ValidateBlock(b) ==
  /\ b.ptype \in {"send", "open", "receive"}
  /\ b.target \in PublicKey
  /\ b.account \in PublicKey
  /\ IF b.ptype = "send" THEN b.amount \in 1..GenesisBalance ELSE b.amount = 0
  /\ (b.ptype = "send") => b.previd \in NodeLedger(\A n \in Node : n)
  /\ (b.ptype = "open") => b.sender \in NodeLedger(\A n \in Node : n)
  /\ (b.ptype = "receive") => b.sender \in NodeLedger(\A n \in Node : n)

CreateGenesisBlock ==
  /\ lastHash = NoHash
  /\ \E k \in PrivateKey :
       /\ lastHash' = CalculateHash(accountBase(PublicKey[k]), NoHash)
       /\ Broadcast(accountBase(PublicKey[k]))
  /\ UNCHANGED <<ledger, received>>

CreateSendBlock(n, amt, r) ==
  /\ \E pre \in accountChain(n) :
       LET h == CalculateHash([account |-> n, ptype |-> "send", previd |-> pre, target |-> r, amount |-> amt], lastHash) IN
       /\ amt \in 1..balanceOverChain(n, accountChain(n))
       /\ lastHash' = h
       /\ Broadcast([account |-> n, ptype |-> "send", previd |-> pre, target |-> r, amount |-> amt])
  /\ UNCHANGED <<ledger, received>>

CreateOpenBlock(n, b) ==
  /\ b.ptype = "send"
  /\ b.target = n
  /\ \A pre \in accountChain(n) : pre.ptype # "open"
  /\ LET h == CalculateHash([account |-> n, ptype |-> "open", previd |-> NoHash, target |-> NoHash, amount |-> 0], lastHash) IN
       /\ lastHash' = h
       /\ Broadcast([account |-> n, ptype |-> "open", previd |-> NoHash, target |-> NoHash, amount |-> 0])
  /\ UNCHANGED <<ledger, received>>

CreateReceiveBlock(n) ==
  /\ \E pre \in accountChain(n), b \in sentBlocks(n) :
       LET h == CalculateHash([account |-> n, ptype |-> "receive", previd |-> pre, target |-> NoHash, amount |-> b.amount], lastHash) IN
       /\ lastHash' = h
       /\ Broadcast([account |-> n, ptype |-> "receive", previd |-> pre, target |-> NoHash, amount |-> b.amount])
  /\ UNCHANGED <<ledger, received>>

CreateChangeRepBlock(n) ==
  /\ \E pre \in accountChain(n) :
       LET h == CalculateHash([account |-> n, ptype |-> "changeRep", previd |-> pre, target |-> NoHash, amount |-> 0], lastHash) IN
       /\ lastHash' = h
       /\ Broadcast([account |-> n, ptype |-> "changeRep", previd |-> pre, target |-> NoHash, amount |-> 0])
  /\ UNCHANGED <<ledger, received>>

Next ==
  \/ CreateGenesisBlock
  \/ \E n \in Node, amt \in 1..GenesisBalance, r \in PublicKey : CreateSendBlock(n, amt, r)
  \/ \E n \in Node, b \in Hash : CreateOpenBlock(n, b)
  \/ \E n \in Node : CreateReceiveBlock(n) \/ CreateChangeRepBlock(n)
  \/ \E n \in Node, b \in received[n] : ProcessBlock(n, b) /\ received' = [received EXCEPT ![n] = received[n] \ {b}]
  \/ \E n \in Node, h \in Hash, b \in NodeLedger(n) : AddToLedger(n, h, b)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ lastHash \in (Hash \cup {NoHash})
  /\ ledger \in [Hash -> [ptype : {"empty", "send", "open", "receive"}, target : PublicKey \cup {NoBlock}]]
  /\ received \in [Node -> SUBSET Hash]

\* Always-valid cryptographic property; the block hash is a record of chain order.
SafetyInvariant ==
  \A h \in Hash :
    ledger[h].ptype # "empty" =>
      ledger[h].previd \in (Hash \cup {NoHash}) /\ ledger[h].target \in PublicKey

====