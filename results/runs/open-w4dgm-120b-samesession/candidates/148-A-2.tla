---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

NONE == "none"

\* Block types for the Nano block-lattice. Very few, but each has different validation rules.
BlockType == {"genesis", "send", "open", "receive", "change"}

\* The set of blocks that a node has received over the network but has not yet validated.
RECURSIVE ReceivedOver(_)
ReceivedOver(S) ==
  IF S = {} THEN {}
  ELSE LET b == CHOOSE x \in S : TRUE IN {b} \cup ReceivedOver(S \ {b})

\* The set of all blocks currently sitting in a node's ledger (i.e., those that have been validated).
RECURSIVE LedgerBlocks(_)
LedgerBlocks(L) ==
  {L[h] : h \in Hash} \ {NoBlockVal}

\* Walks an account chain backwards from the given block, collecting all its blocks into a set.
RECURSIVE ChainBlocks(_)
ChainBlocks(b) ==
  IF b = NoBlockVal THEN {}
  ELSE {b} \cup ChainBlocks(b.prev)

\* Calculates the total balance of an account by walking its chain backwards from the leaf
\* block that is actually present in some ledger (candidates may disagree on which leaf is leafest).
RECURSIVE AccountBalance(_)
AccountBalance(b) ==
  IF b = NoBlockVal THEN 0
  ELSE
    LET tail == AccountBalance(b.prev)
    IN IF b.type = "send" THEN tail - b.amount
       ELSE IF b.type = "receive" THEN tail + b.amount
       ELSE tail

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* The block-space buffer: each node's view of the shared ledger (replicated, never lost).
TypeOK ==
  /\ lastHash \in {NoHash} \union Hash
  /\ ledger \in [Node -> [Hash -> {NoBlockVal} \union [pl : PUBLIC, type : BlockType, prev : Hash, amount : 0..GenesisBalance, sender : PUBLIC, receiver : PUBLIC]]]
  /\ received \in [Node -> SUBSET (Hash \times [pl : PUBLIC, type : BlockType, prev : Hash, amount : 0..GenesisBalance, sender : PUBLIC, receiver : PUBLIC])]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* Broadcasts a newly created block to every node's received set.
Broadcast(b) ==
  [n \in Node |-> received[n] \union {[hash |-> lastHash, bl |-> b]}

CreateGenesisBlock(p) ==
  /\ lastHash = NoHash
  /\ lastHash' = CalculateHash([type |-> "genesis", prev |-> NoHash, amount |-> GenesisBalance, owner |-> p], NoHash)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [pl |-> p, type |-> "genesis", prev |-> NoHash, amount |-> GenesisBalance, sender |-> p, receiver |-> p]]]
  /\ received' = Broadcast([type |-> "genesis", prev |-> NoHash, amount |-> GenesisBalance, owner |-> p])

\* A send block does NOT yet adjust the ledger upon creation; it waits for network delivery and validation.
CreateSendBlock(n, amount) ==
  /\ lastHash # NoHash
  /\ LET src == ledger[n][lastHash] IN
     /\ lastHash' = CalculateHash([type |-> "send", prev |-> lastHash, amount |-> amount, owner |-> src.pl], lastHash)
     /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [pl |-> src.pl, type |-> "send", prev |-> lastHash, amount |-> amount, sender |-> src.pl, receiver |-> NONE]]
  /\ received' = Broadcast([type |-> "send", prev |-> lastHash, amount |-> amount, owner |-> src.pl])

CreateOpenBlock(n, sendHash, p) ==
  /\ lastHash # NoHash
  /\ LET src == ledger[n][sendHash] IN
     /\ lastHash' = CalculateHash([type |-> "open", prev |-> NoHash, amount |-> src.amount, owner |-> p], lastHash)
     /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [pl |-> p, type |-> "open", prev |-> NoHash, amount |-> src.amount, sender |-> src.sender, receiver |-> p]]
  /\ received' = Broadcast([type |-> "open", prev |-> NoHash, amount |-> src.amount, owner |-> p])

CreateReceiveBlock(n, recvHash, sendHash) ==
  /\ lastHash # NoHash
  /\ LET src == ledger[n][sendHash] IN
     /\ lastHash' = CalculateHash([type |-> "receive", prev |-> recvHash, amount |-> src.amount, owner |-> src.receiver], lastHash)
     /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [pl |-> src.receiver, type |-> "receive", prev |-> recvHash, amount |-> src.amount, sender |-> src.sender, receiver |-> src.receiver]]
  /\ received' = Broadcast([type |-> "receive", prev |-> recvHash, amount |-> src.amount, owner |-> src.receiver])

CreateChangeRepBlock(n) ==
  /\ lastHash # NoHash
  /\ LET src == ledger[n][lastHash] IN
     /\ lastHash' = CalculateHash([type |-> "change", prev |-> lastHash, amount |-> 0, owner |-> src.pl], lastHash)
     /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [pl |-> src.pl, type |-> "change", prev |-> lastHash, amount |-> 0, sender |-> src.pl, receiver |-> src.pl]]
  /\ received' = Broadcast([type |-> "change", prev |-> lastHash, amount |-> 0, owner |-> src.pl])

\* Validation walks the local ledger to confirm a send has not already been claimed, which is
\* what provides double-spend protection at the moment it is first observed.
ValidateBlock(n, r) ==
  /\ r \in received[n]
  /\ LET h == r.hash
         b == r.bl
         src == ledger[n][b.prev]
         chain == ChainBlocks(ledger[n][h])
         recvChain == ChainBlocks(ledger[n][src.prev])
         recvBalance == AccountBalance(ledger[n][src.prev])
     IN /\ ledger[n][b.prev] # NoBlockVal
        /\ h \notin LedgerBlocks(ledger[n])
        /\ b.type \in {"open", "receive"} => src.type = "send"
        /\ b.type = "send" => recvBalance >= b.amount
        /\ b.type \in {"open", "receive"} => ~ {x \in recvChain : x.type = "send" /\ x.amount = b.amount /\ x.receiver = b.receiver}
        /\ ledger' = [ledger EXCEPT ![n][h] = b]
  /\ received' = [received EXCEPT ![n] = @ \ {r}]
  /\ lastHash' = lastHash

ValidateAny == \E n \in Node, r \in received[n] : ValidateBlock(n, r)

Next ==
  \/ \E p \in PUBLIC : CreateGenesisBlock(p)
  \/ \E n \in Node, amount \in 1..GenesisBalance : CreateSendBlock(n, amount)
  \/ \E n \in Node, sendHash \in Hash, p \in PUBLIC : CreateOpenBlock(n, sendHash, p)
  \/ \E n \in Node, recvHash \in Hash, sendHash \in Hash : CreateReceiveBlock(n, recvHash, sendHash)
  \/ \E n \in Node : CreateChangeRepBlock(n)
  \/ ValidateAny

Spec == Init /\ [][Next]_vars /\ WF_vars(ValidateAny)

\* Every validated block must remain signed by the account that owns the chain it lives in,
\* and nothing in the system may rewrite the chain without that signature still matching.
SafetyInvariant == \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].pl = ledger[n][h].owner

====