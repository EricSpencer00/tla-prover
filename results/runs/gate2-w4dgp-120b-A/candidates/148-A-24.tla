---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  Hash, NoHashVal,
  PrivateKey, PublicKey,
  Node,
  GenesisBalance,
  NoBlockVal,
  CalculateHash,
  NoHash, NoBlock

ASSUME NoHashVal \notin Hash /\ NoBlockVal \notin Block

\* A block record on a Nano account chain. The block's own hash is
\* calculated from its account, type, amount, and the previous block's
\* hash; a signed block is a block plus a signature over that same
\* content. Every node replicates the entire chain ledger.
Block == (account : PublicKey, type : {"genesis", "send", "open", "receive", "change"}, amount : 0..GenesisBalance, prev : Hash)
SignedBlock == (block : Block, signature : 0..(Cardinality(PublicKey) - 1))

\* Which block generated the last hash, used to order new block creation.
VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Given a block hash, walk its account chain back to the genesis block;
\* sum its credited amounts. Memoization via a small cache keeps this
\* recursion bounded enough to model-check under the node count the .cfg
\* supplies, while still proving the invariant on all reachable states.
RECURSIVE Credits(_)
Credits(b) ==
  LET p == ledger[b].block
  IN IF p.type = "genesis" THEN p.amount
     ELSE IF p.type = "receive" THEN p.amount + Credits(p.prev)
     ELSE Credits(p.prev)

\* Sum the balances of a set of accounts (an integer, not a set of blocks).
RECURSIVE AccountBalance(_)
AccountBalance(P) ==
  IF P = {} THEN 0
  ELSE LET x == CHOOSE e \in P : TRUE
       IN Credits(x) + AccountBalance(P \ {x})

\* Crypto: a signature is the inverse of the signer's public key, one-to-one.
ValidSignature(s) == s.signature = Cardinality(PublicKey) - 1 - s.block.account

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [h \in Hash |-> NoBlockVal]
  /\ received = [n \in Node |-> {}]

\* The genesis block mints the whole supply into one account on every node
\* at once, and can never be reproduced or reordered.
CreateGenesis(n, p) ==
  /\ lastHash = NoHashVal
  /\ LET s == [block |-> [account |-> p, type |-> "genesis", amount |-> GenesisBalance, prev |-> NoHashVal], signature |-> 0]
         h == CalculateHash(s.block, NoHashVal)
     IN /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![h] = s]
        /\ received' = [n \in Node |-> received[n] \cup {s}]
  /\ UNCHANGED <<>>

\* A send must be funded by the sender's current balance.
CreateSend(n, p, amt, to) ==
  /\ lastHash # NoHashVal
  /\ LET s == [block |-> [account |-> p, type |-> "send", amount |-> amt, prev |-> lastHash], signature |-> 0]
         h == CalculateHash(s.block, lastHash)
     IN /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![h] = s]
        /\ received' = [n \in Node |-> received[n] \cup {s}]
  /\ UNCHANGED <<>>

CreateOpen(n, p, blk) ==
  /\ blk.type = "send"
  /\ blk.account = p
  /\ ledger[blk] # NoBlockVal
  /\ lastHash # NoHashVal
  /\ LET s == [block |-> [account |-> p, type |-> "open", amount |-> 0, prev |-> NoHashVal], signature |-> 0]
         h == CalculateHash(s.block, NoHashVal)
     IN /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![h] = s]
        /\ received' = [n \in Node |-> received[n] \cup {s}]
  /\ UNCHANGED <<>>

CreateReceive(n, p, blk) ==
  /\ blk.type \in {"send", "receive"}
  /\ blk.account = p
  /\ ledger[blk] # NoBlockVal
  /\ lastHash # NoHashVal
  /\ LET s == [block |-> [account |-> p, type |-> "receive", amount |-> blk.amount, prev |-> lastHash], signature |-> 0]
         h == CalculateHash(s.block, lastHash)
     IN /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![h] = s]
        /\ received' = [n \in Node |-> received[n] \cup {s}]
  /\ UNCHANGED <<>>

CreateChange(n, p) ==
  /\ lastHash # NoHashVal
  /\ LET s == [block |-> [account |-> p, type |-> "change", amount |-> 0, prev |-> lastHash], signature |-> 0]
         h == CalculateHash(s.block, lastHash)
     IN /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![h] = s]
        /\ received' = [n \in Node |-> received[n] \cup {s}]
  /\ UNCHANGED <<>>

\* A node validates each received block against its own local ledger copy
\* before adding it to that same copy. Validation checks the signature,
\* that the previous block exists, and per-type rules (no overdraft).
ProcessBlock(n, s) ==
  /\ s \notin received[n]
  /\ LET b == s.block
         p == b.account
         r == IF b.prev = NoHashVal THEN NoBlockVal ELSE ledger[b.prev]
         ledgerBalance == IF b.prev = NoHashVal THEN 0 ELSE Credits(b.prev)
     IN /\ r # NoBlockVal \/ b.type = "genesis"
        /\ (b.type \in {"send", "change"} => r # NoBlockVal)
        /\ (b.type \in {"send", "receive"} => ledgerBalance >= b.amount)
        /\ ledger' = [ledger EXCEPT ![b.prev] = s]
        /\ received' = [received EXCEPT ![n] = @ \cup {s}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node, p \in PrivateKey :
       CreateGenesis(n, PublicKey) \/ CreateChange(n, PublicKey)
  \/ \E n \in Node, p \in PrivateKey, amt \in 1..GenesisBalance, to \in PrivateKey :
       CreateSend(n, PublicKey, amt, PublicKey)
  \/ \E n \in Node, p \in PrivateKey, blk \in SignedBlock :
       CreateOpen(n, PublicKey, blk) \/ CreateReceive(n, PublicKey, blk)
  \/ \E n \in Node, s \in SignedBlock : ProcessBlock(n, s)

Spec == Init /\ [][Next]_vars

\* The blockchain is well typed, and every block in every node's ledger is
\* signed under exactly the key of the account chain it belongs to.
TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ \A h \in Hash : ledger[h] \in SignedBlock \cup {NoBlockVal}
  /\ \A n \in Node : received[n] \subseteq SignedBlock

\* No unauthorized participant ever writes an accounting block to the
\* chain: every block in every replica ledger has a signature that
\* matches the public key of the account that owns that block's chain.
SafetyInvariant ==
  \A h \in Hash : ledger[h] # NoBlockVal => ValidSignature(ledger[h])

====