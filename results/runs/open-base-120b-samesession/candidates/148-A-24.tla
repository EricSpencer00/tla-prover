---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  Hash,               \* Set of all possible hash values
  NoHashVal,          \* Sentinel hash indicating "no hash"
  PrivateKey,         \* Set of private keys
  PublicKey,          \* Set of public keys
  Node,               \* Set of network nodes
  GenesisBalance,    \* Nat, total supply at genesis
  NoBlockVal,         \* Sentinel value meaning "no block"
  CalculateHash,      \* Abstract hash function (will be overridden)
  NoHash,             \* Alternative sentinel for hash (kept for compatibility)
  NoBlock             \* Alternative sentinel for block (kept for compatibility)

\* ----------------------------------------------------------------------
\* Operator that will be substituted for the abstract constant CalculateHash.
\* In a concrete model it can be defined as a bounded hash function.
\* Here we simply return a distinguished hash value for any input.
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) == NoHashVal

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
BlockType == {"Genesis", "Send", "Open", "Receive", "Change"}

Block == [
  type          : BlockType,
  account       : PublicKey,      \* owner of the chain this block belongs to
  prevHash      : Hash,           \* hash of the previous block in the chain
  dest          : PublicKey,      \* destination account (for Send/Open)
  amount        : Nat,            \* amount transferred (for Send/Open/Receive)
  representative: PublicKey,     \* voting representative (for Change)
  signature     : STRING          \* abstract signature
]

BlockOrEmpty == UNION {Block, {NoBlockVal}}

\* ----------------------------------------------------------------------
\* Mapping from private keys to their corresponding public keys.
\* This is abstract; any concrete model must provide a function
\* PrivToPub \in [PrivateKey -> PublicKey].
\* ----------------------------------------------------------------------
VARIABLES
  lastHash,            \* the most recent block hash created in the system
  ledger,              \* [Node -> [Hash -> BlockOrEmpty]]
  received,            \* [Node -> SUBSET Hash]  (hashes waiting to be processed)
  blocks,              \* [Hash -> BlockOrEmpty]  (global pool of all created blocks)
  privToPub            \* [PrivateKey -> PublicKey]   (key association)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of all hashes that have a block defined in the global pool.
DefinedHashes == { h \in Hash : blocks[h] # NoBlockVal }

\* A block is considered valid with respect to a node if:
\*   • Its signature matches the public key of the account that owns the chain.
\*   • Its predecessor (if any) already exists in the node's ledger.
\*   • Block‑type specific constraints hold (abstracted as TRUE here).
\* In a detailed model these would be fleshed out.
\* ----------------------------------------------------------------------
ValidSignature(b) ==
  b.signature = b.account \* (placeholder: signature equals the account identifier)

BlockExistsInLedger(node, h) ==
  ledger[node][h] # NoBlockVal

ValidBlockForNode(node, h) ==
  LET b == blocks[h] IN
    /\ b # NoBlockVal
    /\ ValidSignature(b)
    /\ (b.prevHash = NoHashVal \/ BlockExistsInLedger(node, b.prevHash))
    /\ CASE b.type = "Genesis" -> TRUE
       [] b.type = "Send"    -> TRUE
       [] b.type = "Open"    -> TRUE
       [] b.type = "Receive" -> TRUE
       [] b.type = "Change"  -> TRUE

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ lastHash = NoHashVal
  /\ \A n \in Node :
        /\ ledger[n] = [h \in Hash |-> NoBlockVal]
        /\ received[n] = {}
  /\ blocks = [h \in Hash |-> NoBlockVal]
  /\ privToPub \in [PrivateKey -> PublicKey]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Broadcast a newly created block to every node's received set.
Broadcast(h) ==
  /\ \A n \in Node : received' = [received EXCEPT ![n] = @ \cup {h}]
  /\ UNCHANGED <<lastHash, ledger, blocks, privToPub>>

\* Genesis block creation (must happen exactly once).
CreateGenesis ==
  /\ lastHash = NoHashVal
  /\ \E pk \in PublicKey :
        \E sk \in PrivateKey :
          privToPub[sk] = pk
  /\ let newHash == CalculateHashImpl(<<"Genesis", GenesisBalance>>, NoHashVal) in
        /\ newHash \in Hash
        /\ blocks' = [blocks EXCEPT ![newHash] =
              [type |-> "Genesis",
               account |-> privToPub[sk],
               prevHash |-> NoHashVal,
               dest |-> NoHash,
               amount |-> GenesisBalance,
               representative |-> NoHash,
               signature |-> privToPub[sk]]]
        /\ lastHash' = newHash
  /\ UNCHANGED <<ledger, received, privToPub>>
  /\ Broadcast(newHash)

\* Create a send block.
CreateSend ==
  /\ \E sender \in Node :
        \E sk \in PrivateKey :
          privToPub[sk] = senderPub
  /\ \E amount \in Nat :
        amount <= GenesisBalance   \* abstract balance check
  /\ let newHash == CalculateHashImpl(<<"Send", senderPub, amount>>, lastHash) in
        /\ newHash \in Hash
        /\ blocks' = [blocks EXCEPT ![newHash] =
              [type |-> "Send",
               account |-> senderPub,
               prevHash |-> lastHash,
               dest |-> NoHash,
               amount |-> amount,
               representative |-> NoHash,
               signature |-> senderPub]]
        /\ lastHash' = newHash
  /\ UNCHANGED <<ledger, received, privToPub>>
  /\ Broadcast(newHash)

\* Create an open block (opens a new account from a received send).
CreateOpen ==
  /\ \E recipientPub \in PublicKey :
        \E sendHash \in DefinedHashes :
          blocks[sendHash].type = "Send"
          /\ blocks[sendHash].dest = recipientPub
  /\ let newHash == CalculateHashImpl(<<"Open", recipientPub>>, sendHash) in
        /\ newHash \in Hash
        /\ blocks' = [blocks EXCEPT ![newHash] =
              [type |-> "Open",
               account |-> recipientPub,
               prevHash |-> NoHashVal,
               dest |-> recipientPub,
               amount |-> blocks[sendHash].amount,
               representative |-> NoHash,
               signature |-> recipientPub]]
        /\ lastHash' = newHash
  /\ UNCHANGED <<ledger, received, privToPub>>
  /\ Broadcast(newHash)

\* Create a receive block.
CreateReceive ==
  /\ \E receiver \in Node :
        \E sk \in PrivateKey :
          privToPub[sk] = receiverPub
  /\ \E sendHash \in DefinedHashes :
        blocks[sendHash].dest = receiverPub
        /\ blocks[sendHash].type = "Send"
  /\ let newHash == CalculateHashImpl(<<"Receive", receiverPub>>, lastHash) in
        /\ newHash \in Hash
        /\ blocks' = [blocks EXCEPT ![newHash] =
              [type |-> "Receive",
               account |-> receiverPub,
               prevHash |-> lastHash,
               dest |-> NoHash,
               amount |-> blocks[sendHash].amount,
               representative |-> NoHash,
               signature |-> receiverPub]]
        /\ lastHash' = newHash
  /\ UNCHANGED <<ledger, received, privToPub>>
  /\ Broadcast(newHash)

\* Create a change representative block.
CreateChange ==
  /\ \E node \in Node :
        \E sk \in PrivateKey :
          privToPub[sk] = nodePub
  /\ \E newRep \in PublicKey :
        TRUE
  /\ let newHash == CalculateHashImpl(<<"Change", nodePub, newRep>>, lastHash) in
        /\ newHash \in Hash
        /\ blocks' = [blocks EXCEPT ![newHash] =
              [type |-> "Change",
               account |-> nodePub,
               prevHash |-> lastHash,
               dest |-> NoHash,
               amount |-> 0,
               representative |-> newRep,
               signature |-> nodePub]]
        /\ lastHash' = newHash
  /\ UNCHANGED <<ledger, received, privToPub>>
  /\ Broadcast(newHash)

\* Process a received block at a given node.
Process(node) ==
  /\ node \in Node
  /\ \E h \in received[node] :
        /\ ValidBlockForNode(node, h)
  /\ ledger' = [ledger EXCEPT ![node][h] = blocks[h]]
  /\ received' = [received EXCEPT ![node] = @ \ {h}]
  /\ UNCHANGED <<lastHash, blocks, privToPub>>

\* The overall next-state relation.
Next ==
  \/ CreateGenesis
  \/ CreateSend
  \/ CreateOpen
  \/ CreateReceive
  \/ CreateChange
  \/ \E n \in Node : Process(n)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<lastHash, ledger, received, blocks, privToPub>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ lastHash \in Hash
  /\ ledger \in [Node -> [Hash -> BlockOrEmpty]]
  /\ received \in [Node -> SUBSET Hash]
  /\ blocks \in [Hash -> BlockOrEmpty]
  /\ privToPub \in [PrivateKey -> PublicKey]

SafetyInvariant ==
  \A n \in Node :
    \A h \in DefinedHashes :
      /\ ledger[n][h] # NoBlockVal
      => ValidSignature(ledger[n][h])

\* ----------------------------------------------------------------------
\* The set of all invariants to be checked by TLC
\* ----------------------------------------------------------------------
INVARIANTS == TypeInvariant /\ SafetyInvariant

\* The name expected by the .cfg file
SPECIFICATION == Spec

====