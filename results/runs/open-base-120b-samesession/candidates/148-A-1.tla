---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Hash,               \* Set of all possible block hashes
  NoHashVal,          \* Sentinel for “no hash”
  PrivateKey,         \* Set of private keys
  PublicKey,          \* Set of public keys
  Node,               \* Set of network nodes
  GenesisBalance,    \* Total supply of the cryptocurrency (a natural number)
  NoBlockVal,         \* Sentinel for “no block”
  CalculateHash,      \* Abstract hash operator (will be overridden)
  NoHash,             \* Alias for NoHashVal for readability
  NoBlock             \* Alias for NoBlockVal for readability

\* ----------------------------------------------------------------------
\* Helper mappings (abstract, can be instantiated by the .cfg if needed)
\* ----------------------------------------------------------------------
PubOfPriv == [k \in PrivateKey |-> CHOOSE pk \in PublicKey : TRUE]
\* Mapping from a private key to its corresponding public key

OwnerPriv == [n \in Node |-> CHOOSE k \in PrivateKey : TRUE]
\* Mapping from a node to the private key it owns

\* ----------------------------------------------------------------------
\* Block definition
\* ----------------------------------------------------------------------
Block == [ type       : {"genesis","send","open","receive","change"},
           prevHash   : Hash,
           account    : PublicKey,
           dest       : PublicKey,
           amount     : Nat,
           rep        : PublicKey,
           sig        : PrivateKey ]

BlockOrNoBlock == Block \cup { NoBlockVal }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
  lastHash,   \* The most recent block hash (or NoHash)
  ledger,     \* [Node -> [Hash -> BlockOrNoBlock]]
  received,   \* [Node -> SUBSET Hash]  blocks pending validation
  balances    \* [Node -> Nat] current balance of each account

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]
  /\ balances = [n \in Node |-> 0]

\* ----------------------------------------------------------------------
\* Cryptographic primitives (abstract)
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) == CHOOSE h \in Hash : TRUE
\* The concrete implementation will be supplied by the configuration.
CalculateHash(data, prev) == CalculateHashImpl(data, prev)

ValidSignature(b) ==
  /\ b.sig \in PrivateKey
  /\ PubOfPriv[b.sig] = b.account

\* ----------------------------------------------------------------------
\* Helper to update ledger for all nodes with a new block
\* ----------------------------------------------------------------------
AddBlockToAllNodes(newHash, blk) ==
  [n \in Node |-> [h \in Hash |-> IF h = newHash THEN blk ELSE ledger[n][h]]]

Broadcast(newHash) ==
  [n \in Node |-> received[n] \cup {newHash}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CreateGenesis ==
  /\ lastHash = NoHash
  \* Choose a node to act as the genesis creator
  /\ n \in Node
  /\ k \in PrivateKey
  /\ let pk == PubOfPriv[k] in
       /\ blk == [ type     |-> "genesis",
                  prevHash |-> NoHash,
                  account  |-> pk,
                  dest     |-> NoHash,
                  amount   |-> GenesisBalance,
                  rep      |-> NoHash,
                  sig      |-> k ]
  /\ newHash \in Hash
  /\ lastHash' = newHash
  /\ ledger' = AddBlockToAllNodes(newHash, blk)
  /\ received' = [n' \in Node |-> {}]  \* no pending blocks after genesis
  /\ balances' = [balances EXCEPT ![n] = @ + GenesisBalance]

CreateSend ==
  /\ n \in Node
  /\ k == OwnerPriv[n]
  /\ pk == PubOfPriv[k]
  /\ amount \in Nat
  /\ amount <= balances[n]
  /\ dest \in PublicKey
  /\ let blk == [ type     |-> "send",
                  prevHash |-> lastHash,
                  account  |-> pk,
                  dest     |-> dest,
                  amount   |-> amount,
                  rep      |-> NoHash,
                  sig      |-> k ] in
       /\ newHash \in Hash
       /\ lastHash' = newHash
       /\ ledger' = AddBlockToAllNodes(newHash, blk)
       /\ received' = Broadcast(newHash)
       /\ balances' = [balances EXCEPT ![n] = @ - amount]

CreateOpen ==
  /\ n \in Node
  /\ k == OwnerPriv[n]
  /\ pk == PubOfPriv[k]
  /\ srcHash \in Hash
  /\ blkSrc == ledger[n][srcHash]
  /\ blkSrc # NoBlockVal
  /\ blkSrc.type = "send"
  /\ blkSrc.dest = pk
  /\ let blk == [ type     |-> "open",
                  prevHash |-> NoHash,
                  account  |-> pk,
                  dest     |-> NoHash,
                  amount   |-> blkSrc.amount,
                  rep      |-> NoHash,
                  sig      |-> k ] in
       /\ newHash \in Hash
       /\ lastHash' = newHash
       /\ ledger' = AddBlockToAllNodes(newHash, blk)
       /\ received' = Broadcast(newHash)
       /\ balances' = [balances EXCEPT ![n] = @ + blkSrc.amount]

CreateReceive ==
  /\ n \in Node
  /\ k == OwnerPriv[n]
  /\ pk == PubOfPriv[k]
  /\ srcHash \in Hash
  /\ blkSrc == ledger[n][srcHash]
  /\ blkSrc # NoBlockVal
  /\ blkSrc.type = "send"
  /\ blkSrc.dest = pk
  /\ let blk == [ type     |-> "receive",
                  prevHash |-> lastHash,
                  account  |-> pk,
                  dest     |-> NoHash,
                  amount   |-> blkSrc.amount,
                  rep      |-> NoHash,
                  sig      |-> k ] in
       /\ newHash \in Hash
       /\ lastHash' = newHash
       /\ ledger' = AddBlockToAllNodes(newHash, blk)
       /\ received' = Broadcast(newHash)
       /\ balances' = [balances EXCEPT ![n] = @ + blkSrc.amount]

CreateChange ==
  /\ n \in Node
  /\ k == OwnerPriv[n]
  /\ pk == PubOfPriv[k]
  /\ newRep \in PublicKey
  /\ let blk == [ type     |-> "change",
                  prevHash |-> lastHash,
                  account  |-> pk,
                  dest     |-> NoHash,
                  amount   |-> 0,
                  rep      |-> newRep,
                  sig      |-> k ] in
       /\ newHash \in Hash
       /\ lastHash' = newHash
       /\ ledger' = AddBlockToAllNodes(newHash, blk)
       /\ received' = Broadcast(newHash)
       /\ UNCHANGED balances

ProcessBlock ==
  /\ n \in Node
  /\ h \in received[n]
  /\ blk == ledger[n][h]
  /\ blk # NoBlockVal
  /\ ValidSignature(blk)
  /\ lastHash' = lastHash
  /\ ledger' = ledger
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED balances

Next ==
  \/ CreateGenesis
  \/ CreateSend
  \/ CreateOpen
  \/ CreateReceive
  \/ CreateChange
  \/ ProcessBlock

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received, balances>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ lastHash \in Hash \/ lastHash = NoHash
  /\ ledger \in [Node -> [Hash -> BlockOrNoBlock]]
  /\ received \in [Node -> SUBSET Hash]
  /\ balances \in [Node -> Nat]

SafetyInvariant ==
  /\ \A n \in Node :
        \A h \in Hash :
          LET blk == ledger[n][h] IN
            blk # NoBlockVal =>
              /\ blk.type \in {"genesis","send","open","receive","change"}
              /\ ValidSignature(blk)

\* ----------------------------------------------------------------------
\* Exported identifiers for the model checker
\* ----------------------------------------------------------------------
\* The .cfg file will refer to these names.
\* (No additional definitions are required.)
====