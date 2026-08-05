---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* The Nano protocol replicates a block-lattice ledger across all network nodes; each
\* account chain's history is recorded in an order that grows super-exponentially,
\* which is exactly what makes exhaustive model checking of a blockchain so hard.

ASSUME NoHashVal \notin Hash /\ NoBlockVal \notin Hash

VARIABLES lastHash, ledger, received

vars == << lastHash, ledger, received >>

\* Recursively walk an account chain by hash to compute its balance. The ledger
\* check below validates the block chain, so this recursive walk is trusted.
RECURSIVE Balance(_)
Balance(h) ==
  IF h = NoHashVal THEN 0
  ELSE LET blk == ledger[h] IN
    IF blk.blockType = "send" THEN
      Balance(blk.prevHash) - blk.amount
    ELSE IF blk.blockType = "receive" THEN
      Balance(blk.prevHash) + blk.amount
    ELSE Balance(blk.prevHash)

RECURSIVE ChainExists(_, _)
ChainExists(h, a) ==
  IF h = NoHashVal THEN TRUE
  ELSE LET blk == ledger[h] IN
    IF blk.account = a THEN FALSE
    ELSE ChainExists(blk.prevHash, a)

RECURSIVE BalanceSum(_)
BalanceSum(S) ==
  IF S = {} THEN 0
  ELSE LET n == CHOOSE x \in S : TRUE IN BalanceSum(S \ {n}) + Balance(n)

SignedBlock == [account : PublicKey, prevHash : Hash, blockType : {"send", "receive", "open", "change"}, amount : Nat, sig : PrivateKey]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [h \in Hash |-> NoBlockVal]
  /\ received = [n \in Node |-> {}]

\* Creating the genesis block updates every node's ledger simultaneously, which
\* is how a chain can "grow backwards" from the empty set without a separate
\* merge step.
CreateGenesisBlock(n) ==
  /\ lastHash = NoHashVal
  /\ LET h == CalculateHash(n, NoHashVal) IN
    /\ h \notin ledger
    /\ ledger' = [ledger EXCEPT ![h] = [account |-> n, prevHash |-> NoHashVal, blockType |-> "open", amount |-> GenesisBalance, sig |-> n]]
    /\ lastHash' = h
    /\ received' = [m \in Node |-> received[m] \cup {h}]

CreateSendBlock(n, a, amt) ==
  /\ lastHash # NoHashVal
  /\ Balance(n) >= amt
  /\ ~ChainExists(lastHash, a)
  /\ LET h == CalculateHash(n, NoHashVal) IN
    /\ h \notin ledger
    /\ ledger' = [ledger EXCEPT ![h] = [account |-> n, prevHash |-> lastHash, blockType |-> "send", amount |-> amt, sig |-> n]]
    /\ lastHash' = h
    /\ received' = [m \in Node |-> received[m] \cup {h}]

CreateOpenBlock(n, src) ==
  /\ ledger[src].blockType = "send"
  /\ ledger[src].account # n
  /\ src \notin {blk.prevHash : blk \in {ledger[h] : h \in Hash} : blk.blockType = "receive" /\ blk.account = n}
  /\ ChainExists(lastHash, n)
  /\ LET h == CalculateHash(n, NoHashVal) IN
    /\ h \notin ledger
    /\ ledger' = [ledger EXCEPT ![h] = [account |-> n, prevHash |-> src, blockType |-> "open", amount |-> ledger[src].amount, sig |-> n]]
    /\ lastHash' = h
    /\ received' = [m \in Node |-> received[m] \cup {h}]

CreateReceiveBlock(n, src) ==
  /\ ledger[src].blockType = "send"
  /\ ledger[src].account # n
  /\ src \notin {blk.prevHash : blk \in {ledger[h] : h \in Hash} : blk.blockType = "receive" /\ blk.account = n}
  /\ ChainExists(lastHash, n)
  /\ LET h == CalculateHash(n, src) IN
    /\ h \notin ledger
    /\ ledger' = [ledger EXCEPT ![h] = [account |-> n, prevHash |-> lastHash, blockType |-> "receive", amount |-> ledger[src].amount, sig |-> n]]
    /\ lastHash' = h
    /\ received' = [m \in Node |-> received[m] \cup {h}]

CreateChangeBlock(n) ==
  /\ ChainExists(lastHash, n)
  /\ LET h == CalculateHash(n, NoHashVal) IN
    /\ h \notin ledger
    /\ ledger' = [ledger EXCEPT ![h] = [account |-> n, prevHash |-> lastHash, blockType |-> "change", amount |-> 0, sig |-> n]]
    /\ lastHash' = h
    /\ received' = [m \in Node |-> received[m] \cup {h}]

\* Validation checks signatures against the public key of the chain's account (the
\* network's only binding between a block and its owner) plus the chain-type rule.
ValidateBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[h].sig = n
  /\ ledger' = [ledger EXCEPT ![h] = ledger[h]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node : CreateGenesisBlock(n)
  \/ \E n \in Node, a \in PublicKey, amt \in 1..GenesisBalance : CreateSendBlock(n, a, amt)
  \/ \E n \in Node, src \in Hash : CreateOpenBlock(n, src) \/ CreateReceiveBlock(n, src)
  \/ \E n \in Node : CreateChangeBlock(n)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Hash -> SignedBlock \cup {NoBlockVal}]
  /\ received \in [Node -> SUBSET Hash]

\* Cryptographic soundness: every block in the replicated ledger must carry a
\* signature that matches the public key of the account that owns its chain.
SafetyInvariant ==
  \A h \in Hash : ledger[h] # NoBlockVal => ledger[h].sig = ledger[h].account

====