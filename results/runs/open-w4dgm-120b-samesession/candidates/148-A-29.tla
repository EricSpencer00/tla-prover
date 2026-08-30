---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME NoHash \notin Hash
ASSUME NoHashVal \notin Hash
ASSUME NoBlock \notin (Hash \X PrivateKey \X PublicKey \X (Hash \cup {NoHash}))
ASSUME NoBlockVal \notin (Hash \X PrivateKey \X PublicKey \X (Hash \cup {NoHash}))

OwnedKey == [n \in Node |-> CHOOSE e \in PrivateKey : PublicKey[e] = n]

VARIABLES lastHash, ledger, received
vars == <<lastHash, ledger, received>>

\* Each node's ledger maps block hashes to signed blocks (or NoBlock as an empty sentinel).
\* A block records its creator, its account, and the previous block in that account's chain.
\* Ed25519-style signatures are modeled as the creator's public key, which must match the
\* account's public key for the block to be valid.
\* Blake2b-style hashes order the blocks on each account chain and are modeled abstractly
\* so the block set stays finite and the model solvable.

RECURSIVE Balance(_)
Balance(g) == IF g = NoHash THEN 0
              ELSE
                LET b == ledger[NoHash][g] IN
                  IF b = NoBlock THEN 0
                  ELSE IF b[3] = "send" THEN -b[2] + Balance(b[1])
                  ELSE IF b[3] = "receive" THEN b[2] + Balance(b[1])
                  ELSE Balance(b[1])

RECURSIVE TotalBalance(_)
TotalBalance(S) ==
  IF S = {} THEN 0
  ELSE
    LET g == CHOOSE x \in S : TRUE IN
      Balance(g) + TotalBalance(S \ {g})

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> (Hash \X PrivateKey \X PublicKey \X (Hash \cup {NoHash} \cup {"send", "receive", "change", "genesis"} \cup {NoBlock})]]]
  /\ received \in [Node -> SUBSET (Hash \X PrivateKey \X PublicKey \X (Hash \cup {NoHash} \cup {"send", "receive", "change", "genesis"} \cup {NoBlock}))]

\* Every block in every node's ledger must carry a signature that matches the public key
\* of the account the block belongs to -- the core cryptographic claim about the chain.
SafetyInvariant ==
  \A n \in Node, g \in Hash :
    IF ledger[n][g] = NoBlock THEN TRUE
    ELSE ledger[n][g][3] = PublicKey[OwnedKey[n]]

LedgerConsistent ==
  \A n, m \in Node, g \in Hash :
    (ledger[n][g] # NoBlock /\ ledger[m][g] # NoBlock) => ledger[n][g] = ledger[m][g]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [g \in Hash |-> NoBlock]]
  /\ received = [n \in Node |-> {}]

\* The genesis block seeds the blockchain with the entire coin supply and is written to
\* every node's ledger the moment it is created.
CreateGenesisBlock ==
  /\ lastHash = NoHash
  /\ \E e \in PrivateKey :
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![NoHash] = <<NoHash, e, PublicKey[e], "genesis", GenesisBalance>>]
  /\ lastHash' = NoHash
  /\ received' = [n \in Node |-> {}]

CreateSendBlock(sender, rec, amt) ==
  /\ lastHash # NoHash
  /\ ledger[sender][lastHash] # NoBlock
  /\ amt \in 1..GenesisBalance
  /\ amt <= Balance(lastHash)
  /\ \E e \in PrivateKey :
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash] = <<lastHash, e, PublicKey[OwnedKey[n]], "send", amt>>]
       /\ lastHash' = CalculateHashImpl(<<sender, rec, amt>>, lastHash)
  /\ received' = [n \in Node |-> received[n] \cup {[sender EXCEPT ![1] = lastHash], e, PublicKey[OwnedKey[n]], "send", amt}}]

\* An open block is the first block in a new account chain and must reference an incoming
\* send that has not already been claimed by another open block.
CreateOpenBlock(node, sendHash) ==
  /\ lastHash # NoHash
  /\ ledger[node][lastHash] # NoBlock
  /\ \E e \in PrivateKey :
       /\ \A n \in Node : ledger[n][sendHash] # NoBlock => ledger[n][sendHash][3] = "send"
       /\ \A n' \in Node : ~(\A g \in Hash : g = sendHash => ledger[n'][g] = <<sendHash, e, PublicKey[OwnedKey[n']], "open", NoBlockVal>>)
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash] = <<sendHash, e, PublicKey[OwnedKey[n]], "open", NoBlockVal>>]
       /\ lastHash' = CalculateHashImpl(sendHash, lastHash)
  /\ received' = [n \in Node |-> received[n] \cup {[sendHash EXCEPT ![1] = lastHash], e, PublicKey[OwnedKey[n]], "open", NoBlockVal}}]

CreateReceiveBlock(node, recvHash, sendHash) ==
  /\ lastHash # NoHash
  /\ ledger[node][lastHash] # NoBlock
  /\ \E e \in PrivateKey :
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash] = <<recvHash, e, PublicKey[OwnedKey[n]], "receive", NoBlockVal>>]
       /\ lastHash' = CalculateHashImpl(<<recvHash, sendHash>>, lastHash)
  /\ received' = [n \in Node |-> received[n] \cup {[recvHash EXCEPT ![1] = lastHash], e, PublicKey[OwnedKey[n]], "receive", sendHash}}]

CreateChangeBlock(node) ==
  /\ lastHash # NoHash
  /\ ledger[node][lastHash] # NoBlock
  /\ \E e \in PrivateKey :
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash] = <<lastHash, e, PublicKey[OwnedKey[n]], "change", NoBlockVal>>]
       /\ lastHash' = CalculateHashImpl(lastHash, lastHash)
  /\ received' = [n \in Node |-> received[n] \cup {[lastHash EXCEPT ![1] = lastHash], e, PublicKey[OwnedKey[n]], "change", NoBlockVal}}]

\* Validation checks the signature against the account's public key and the internal
\* references (prev block, send block) against the node's own ledger copy.
Validate(n, blk) ==
  /\ blk \in received[n]
  /\ ledger[n][blk[1]] = NoBlock
  /\ blk[3] \in {"send", "receive", "change", "genesis"}
  /\ blk[2] = PublicKey[OwnedKey[n]]
  /\ IF blk[3] = "send" THEN ledger[n][blk[1]] # NoBlock
     ELSE IF blk[3] = "receive" THEN ledger[n][blk[4]] = NoBlock
     ELSE TRUE
  /\ ledger' = [ledger EXCEPT ![n][blk[1]] = blk]
  /\ received' = [received EXCEPT ![n] = @ \ {blk}]
  /\ UNCHANGED lastHash

ValidateAny == \E n \in Node, blk \in received[n] : Validate(n, blk)

Next ==
  \/ CreateGenesisBlock
  \/ \E n \in Node, e \in PrivateKey : CreateSendBlock(n, PublicKey[e], 1)
  \/ \E n \in Node, e \in PrivateKey : CreateSendBlock(n, PublicKey[e], GenesisBalance)
  \/ \E n \in Node, g \in Hash : CreateOpenBlock(n, g)
  \/ \E n \in Node, g, h \in Hash : CreateReceiveBlock(n, g, h)
  \/ \E n \in Node : CreateChangeBlock(n)
  \/ ValidateAny

Spec == Init /\ [][Next]_vars /\ WF_vars(ValidateAny)

\* The total balance across all account chains never exceeds the genesis balance.
BalanceInvariant == TotalBalance({g \in Hash : ledger[NoHash][g] # NoBlock}) <= GenesisBalance

====