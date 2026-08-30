---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME NoHash \notin Hash
ASSUME NoBlock \in Block
ASSUME NoHashVal \notin Hash
ASSUME GenesisBalance \in Nat

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Block]]
  /\ received \in [Node -> SUBSET Block]

AccToPublic == [k \in PrivateKey |-> CHOOSE p \in PublicKey : Acc(p) = Acc(k)]

RECURSIVE SumAmounts(_)
SumAmounts(S) ==
  IF S = {} THEN 0
  ELSE LET h == CHOOSE x \in S : TRUE IN ledger[NoBlock].amount[h] + SumAmounts(S \ {h})

AccountBalance(node, h) ==
  IF h = NoHash THEN 0
  ELSE
    IF ledger[node][h] = NoBlockVal THEN AccountBalance(node, ledger[node][h].prev)
    ELSE IF ledger[node][h].type = "send" THEN AccountBalance(node, ledger[node][h].prev)
    ELSE IF ledger[node][h].type \in {"open", "receive", "change"} THEN ledger[node][h].amount + AccountBalance(node, ledger[node][h].prev)
    ELSE AccountBalance(node, ledger[node][h].prev)

Init =
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [g \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

SignatureValid(b) == AccToPublic(b.key) = b.account

ValidateBlock(node, b) ==
  /\ SignatureValid(b)
  /\ IF b.type = "send" THEN
       AccountBalance(node, b.prev) >= b.amount /\ b.dest \notin NoHash
     ELSE IF b.type = "open" THEN
       \E s \in Hash : ledger[NoBlock][s] # NoBlockVal /\ ledger[NoBlock][s].dest = node /\ s \notin Hash
     ELSE IF b.type = "receive" THEN
       \E s \in Hash : ledger[NoBlock][s] # NoBlockVal /\ ledger[NoBlock][s].dest = node /\ s \notin Hash
     ELSE TRUE
  /\ b.prev \in Hash \/ b.prev = NoHash

CreateGenesisBlock ==
  /\ lastHash = NoHash
  /\ \E k \in PrivateKey :
       /\ \A n \in Node : ledger[n] = [g \in Hash |-> NoBlockVal]
       /\ LET h == CalculateHash(k, NoHash) IN
            /\ lastHash' = h
            /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = [type |-> "open", prev |-> NoHash, account |-> node, dest |-> node, amount |-> GenesisBalance, key |-> k]]]
  /\ UNCHANGED received

CreateSendBlock ==
  /\ \E n \in Node, k \in PrivateKey, destNode \in Node, amt \in (Nat \ {0}) :
       /\ AccountBalance(n, lastHash) >= amt
       /\ LET h == CalculateHash(k, lastHash) IN
            /\ lastHash' = h
            /\ ledger' = [ledger EXCEPT ![n][h] = [type |-> "send", prev |-> lastHash, account |-> node, dest |-> destNode, amount |-> amt, key |-> k]]
            /\ received' = [m \in Node |-> IF m = n THEN received[m] ELSE received[m] \cup {[type |-> "send", prev |-> lastHash, account |-> node, dest |-> destNode, amount |-> amt, key |-> k]}]
  /\ UNCHANGED <<>>

CreateOpenBlock ==
  /\ \E n \in Node, k \in PrivateKey :
       LET h == CalculateHash(k, lastHash) IN
            /\ lastHash' = h
            /\ ledger' = [ledger EXCEPT ![n][h] = [type |-> "open", prev |-> lastHash, account |-> node, dest |-> node, amount |-> 0, key |-> k]]
            /\ received' = [m \in Node |-> IF m = n THEN received[m] ELSE received[m] \cup {[type |-> "open", prev |-> lastHash, account |-> node, dest |-> node, amount |-> 0, key |-> k]}]

CreateReceiveBlock ==
  /\ \E n \in Node, k \in PrivateKey, srcNode \in Node, amt \in (Nat \ {0}) :
       LET h == CalculateHash(k, lastHash) IN
            /\ lastHash' = h
            /\ ledger' = [ledger EXCEPT ![n][h] = [type |-> "receive", prev |-> lastHash, account |-> node, dest |-> node, amount |-> amt, key |-> k]]
            /\ received' = [m \in Node |-> IF m = n THEN received[m] ELSE received[m] \cup {[type |-> "receive", prev |-> lastHash, account |-> node, dest |-> node, amount |-> amt, key |-> k]}]

CreateChangeRepBlock ==
  /\ \E n \in Node, k \in PrivateKey :
       LET h == CalculateHash(k, lastHash) IN
            /\ lastHash' = h
            /\ ledger' = [ledger EXCEPT ![n][h] = [type |-> "change", prev |-> lastHash, account |-> node, dest |-> node, amount |-> 0, key |-> k]]
            /\ received' = [m \in Node |-> IF m = n THEN received[m] ELSE received[m] \cup {[type |-> "change", prev |-> lastHash, account |-> node, dest |-> node, amount |-> 0, key |-> k]}]

ProcessReceivedBlock ==
  /\ \E n \in Node, m \in Node, b \in received[n] :
       /\ ValidateBlock(m, b)
       /\ ledger' = [ledger EXCEPT ![m][CalculateHash(b.key, b.prev)] = b]
       /\ received' = [received EXCEPT ![n] = received[n] \ {b}]
  /\ UNCHANGED lastHash

Next ==
  \/ CreateGenesisBlock \/ CreateSendBlock \/ CreateOpenBlock \/ CreateReceiveBlock \/ CreateChangeRepBlock
  \/ ProcessReceivedBlock

Spec == Init /\ [][Next]_vars

SafetyInvariant == \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => SignatureValid(ledger[n][h])

====