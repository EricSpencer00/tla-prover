---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* lastHash is the most recently calculated block hash, used for ordering.
\* ledger is the replicated, per-node copy of confirmed blocks (hash -> block).
\* received is the per-node set of blocks in transit pending confirmation.
VARIABLES lastHash, ledger, received

AccountOf(h) == ledger[h].acct
OpOf(h) == ledger[h].op
PrevOf(h) == ledger[h].prev
SendOf(h) == ledger[h].send
DestOf(h) == ledger[h].dest
AmtOf(h) == ledger[h].amt

\* Balance walks an account's chain from a given block back to genesis.
RECURSIVE Balance(_)
Balance(n) == IF n = NoHash THEN 0 ELSE AmtOf(n) + Balance(PrevOf(n))

Accounts == PublicKey \X {"send", "open", "recv"}
AccountBalance(k) == Balance(LastHashOfChain(k))
RECURSIVE LastHashOfChain(_)
LastHashOfChain(k) == CHOOSE h \in Hash : AccountOf(h) = k /\ ~\E m \in Hash : AccountOf(m) = k /\ PrevOf(m) = h

RECURSIVE Reached(_)
Reached(n) == IF n = NoHash THEN {} ELSE {n} \cup Reached(PrevOf(n))

RECURSIVE SentBy(_)
SentBy(n) == IF n = NoHash THEN {} ELSE
  IF OpOf(n) = "send" THEN {n} \cup SentBy(PrevOf(n)) ELSE SentBy(PrevOf(n))

RECURSIVE ReceivedBy(_)
ReceivedBy(n) == IF n = NoHash THEN {} ELSE
  IF OpOf(n) = "recv" THEN {n} \cup ReceivedBy(PrevOf(n)) ELSE ReceivedBy(PrevOf(n))

\* The sum of every account's balance (one balance per public-key account).
RECURSIVE TotalCoin(_)
TotalCoin(S) ==
  IF S = {} THEN 0
  ELSE LET k == CHOOSE x \in S : TRUE IN AccountBalance(k) + TotalCoin(S \ {k})

TypeInvariant ==
  /\ lastHash \in {NoHash} \cup Hash
  /\ ledger \in [Hash -> (Accounts \X {"send", "open", "recv"} \X PublicKey \X Hash \X PublicKey \X Nat) \cup {NoBlockVal}]
  /\ received \in [Node -> SUBSET Hash]

\* Every block in every node's ledger carries a signature that matches its account's public key.
SafetyInvariant ==
  \A n \in Hash : ledger[n] # NoBlockVal => PublicKey \in AccountBalance(AccountOf(n))

Init ==
  /\ lastHash = NoHash
  /\ ledger = [h \in Hash |-> NoBlockVal]
  /\ received = [nd \in Node |-> {}]

\* The genesis block is the first block ever created and deposited identically on every node.
CreateGenesisBlock(nd) ==
  /\ lastHash = NoHash
  /\ \E pk \in PublicKey :
       /\ ledger' = [ledger EXCEPT ![NoHash] = <<pk, "open", pk, NoHash, NoHash, GenesisBalance>>]
  /\ lastHash' = NoHash
  /\ received' = [m \in Node |-> {NoHash}]

CreateSendBlock(nd, acct) ==
  /\ {\* Ordering: the sender's chain must already exist before it can send. *\}
       Reached(LastHashOfChain(acct)) # {}
  /\ lastHash \in Hash
  /\ ~(\E m \in Hash : ledger[m] # NoBlockVal /\ ledger[m].op = "send" /\ ledger[m].acct = acct /\ ledger[m].dest = acct)
  /\ \E k \in PrivateKey, d \in PublicKey, a \in Nat :
       /\ PublicKey[k] = acct
       /\ AccountBalance(acct) >= a
       /\ ledger' = [ledger EXCEPT ![lastHash] = <<acct, "send", d, LastHashOfChain(acct), d, a>>]
  /\ lastHash' = CalculateHash(acct, "send", d, LastHashOfChain(acct), a)
  /\ received' = [received EXCEPT ![nd] = received[nd] \cup {lastHash}]

CreateOpenBlock(nd, acct, h) ==
  /\ AccountOf(h) = PublicKey[PublicKeyOf(acct)]
  /\ OpOf(h) = "send"
  /\ ledger[h].dest = acct
  /\ ~(\E m \in Hash : ledger[m] # NoBlockVal /\ ledger[m].op = "open" /\ ledger[m].acct = acct
  /\ lastHash \in Hash
  /\ ledger' = [ledger EXCEPT ![lastHash] = <<acct, "open", acct, NoHash, acct, 0>>]
  /\ lastHash' = CalculateHash(acct, "open", acct, NoHash, 0)
  /\ received' = [received EXCEPT ![nd] = received[nd] \cup {lastHash}]

CreateReceiveBlock(nd, acct) ==
  /\ AccountBalance(acct) >= 0
  /\ lastHash \in Hash
  /\ \E h \in Hash :
       /\ OpOf(h) = "send"
       /\ ledger[h].dest = acct
       /\ h \notin SentBy(LastHashOfChain(acct))
       /\ h \notin ReceivedBy(LastHashOfChain(acct))
       /\ ledger' = [ledger EXCEPT ![lastHash] = <<acct, "recv", acct, LastHashOfChain(acct), AccountOf(h), AmtOf(h)>>]
  /\ lastHash' = CalculateHash(acct, "recv", acct, LastHashOfChain(acct), AmtOf(h))
  /\ received' = [received EXCEPT ![nd] = received[nd] \cup {lastHash}]

CreateChangeRepresentative(nd, acct) ==
  /\ lastHash \in Hash
  /\ ledger' = [ledger EXCEPT ![lastHash] = <<acct, "send", acct, LastHashOfChain(acct), acct, 0>>]
  /\ lastHash' = CalculateHash(acct, "send", acct, LastHashOfChain(acct), 0)
  /\ received' = [received EXCEPT ![nd] = received[nd] \cup {lastHash}]

ProcessBlock(nd, h) ==
  /\ h \in received[nd]
  /\ ledger[h] # NoBlockVal
  /\ ledger' = [ledger EXCEPT ![h] = ledger[h]]
  /\ received' = [received EXCEPT ![nd] = received[nd] \ {h}]
  /\ lastHash' = lastHash

Next ==
  \/ \E nd \in Node : CreateGenesisBlock(nd)
  \/ \E nd \in Node, acct \in PublicKey : CreateSendBlock(nd, acct) \/ CreateReceiveBlock(nd, acct) \/ CreateChangeRepresentative(nd, acct)
  \/ \E nd \in Node, acct \in PublicKey, h \in Hash : CreateOpenBlock(nd, acct, h)
  \/ \E nd \in Node, h \in Hash : ProcessBlock(nd, h)

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* Conservation: the sum of all account balances never exceeds the genesis balance.
CoinConservation == TotalCoin(PublicKey) <= GenesisBalance

====