---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, TLC

\* A Nano block-lattice, where every account owns its own chain of blocks.
\* Each block is a signed message carrying the previous block on that account's chain.
\* The model focuses on cryptographic signatures and on the hash-based ordering of blocks.
CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Sum of all account balances (recursive walk of every chain; used for a balance invariant)
RECURSIVE Balance(_)
Balance(n) == IF n = 0 THEN 0 ELSE Balance(n - 1) + BalanceOf(n, n)

\* Balance of account n as derived from its chain; walks the chain from hash back to the genesis block
RECURSIVE BalanceOf(_, _)
BalanceOf(0, h) == 0
BalanceOf(n, h) == IF ledger[n][h] = NoBlockVal THEN 0
                   ELSE IF h = NoHash THEN 0
                   ELSE LET blk == ledger[n][h] IN
                     (IF blk.type = "send" THEN -blk.amount
                      ELSIF blk.type = "receive" THEN blk.amount
                      ELSE 0) + BalanceOf(n, blk.prevHash)

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> {NoBlockVal} \cup (PUBLIC_KEY \X PUBLIC_KEY \X Nat \X Hash \X Hash \X {"send", "open", "receive", "change"})]]
  /\ received \in [Node -> SUBSET Hash]

\* Every block recorded by every node must carry a signature matching the account's public key
\* (the account owning the chain the block belongs to)
SafetyInvariant ==
  \A n \in Node, h \in Hash :
    /\ (ledger[n][h] # NoBlockVal) => (ledger[n][h].sig = ledger[n][h].from)
    /\ (ledger[n][h] # NoBlockVal) => ((ledger[n][h].type \in {"send", "receive"}) => ledger[n][h].to # NoHash)

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock == \E k \in PrivateKey :
  /\ lastHash = NoHashVal
  /\ lastHash' = CalculateHash(lastHash, "genesis", k, NoHash, NoHash)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash] = {<<k, NoHash, GenesisBalance, NoHash, NoHash, "open">>}]]
  /\ received' = [n \in Node |-> {lastHash}]

\* A node creates a block debiting its own account; the amount must not exceed its balance
CreateSendBlock == \E k \in PrivateKey, n \in Node, tar \in PublicKey, amt \in 1..GenesisBalance :
  /\ lastHash # NoHashVal
  /\ Balance(n) >= amt
  /\ lastHash' = CalculateHash(lastHash, "send", k, tar, NoHash, amt)
  /\ ledger' = [ledger EXCEPT ![n][lastHash] = {<<k, tar, amt, lastHash, NoHash, "send">>}]
  /\ received' = [n \in Node |-> received[n] \cup {lastHash}]

\* Opening a new account refers to a send block directed to this account
CreateOpenBlock == \E k \in PrivateKey, n \in Node, s \in Hash :
  /\ ledger[n][s] # NoBlockVal
  /\ ledger[n][s].type = "send"
  /\ ledger[n][s].to = NoHash
  /\ lastHash' = CalculateHash(lastHash, "open", k, NoHash, NoHash, 0)
  /\ ledger' = [ledger EXCEPT ![n][lastHash] = {<<k, NoHash, 0, NoHash, NoHash, "open">>}]
  /\ received' = [n \in Node |-> received[n] \cup {lastHash}]

\* A node receives credits by creating a receive block for a pending send
CreateReceiveBlock == \E k \in PrivateKey, n \in Node, s \in Hash :
  /\ ledger[n][s] # NoBlockVal
  /\ ledger[n][s].type = "receive"
  /\ ledger[n][s].to = NoHash
  /\ lastHash' = CalculateHash(lastHash, "receive", k, NoHash, s, ledger[n][s].amount)
  /\ ledger' = [ledger EXCEPT ![n][lastHash] = {<<k, NoHash, ledger[n][s].amount, NoHash, s, "receive">>}]
  /\ received' = [n \in Node |-> received[n] \cup {lastHash}]

\* A node changes its voting representative
CreateChangeRepresentative == \E k \in PrivateKey, n \in Node :
  /\ lastHash' = CalculateHash(lastHash, "change", k, NoHash, NoHash, 0)
  /\ ledger' = [ledger EXCEPT ![n][lastHash] = {<<k, NoHash, 0, lastHash, NoHash, "change">>}]
  /\ received' = [n \in Node |-> received[n] \cup {lastHash}]

\* A node validates and applies a received block to its own copy of the ledger
ValidateBlock == \E n \in Node, h \in Hash :
  /\ h \in received[n]
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][ledger[n][h].prevHash] # NoBlockVal
  /\ ledger' = [ledger EXCEPT ![n][h] = ledger[n][h]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ CreateGenesisBlock
  \/ CreateSendBlock
  \/ CreateOpenBlock
  \/ CreateReceiveBlock
  \/ CreateChangeRepresentative
  \/ ValidateBlock

Spec == Init /\ [][Next]_vars

\* The sum of all account balances can never exceed the original genesis balance.
\* (Defined here, separate from TypeInvariant and SafetyInvariant.)
BalanceBound == Balance(Node) <= GenesisBalance

====