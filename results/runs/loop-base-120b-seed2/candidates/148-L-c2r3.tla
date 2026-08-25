---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash,                 \* Set of all possible block hashes
    NoHashVal,            \* Sentinel value indicating no hash exists yet
    PrivateKey,           \* Set of private keys
    PublicKey,            \* Set of public keys
    Node,                 \* Set of network nodes
    GenesisBalance,       \* Total supply of coins at genesis
    NoBlockVal,           \* Sentinel for a non‑existent block
    CalculateHash,        \* Abstract hash operator (overridden by CalculateHashImpl)
    NoHash,               \* Sentinel hash used inside blocks
    NoBlock,              \* Sentinel block value
    PrivateKeyToPublic,   \* Mapping from private keys to public keys
    NodeOwnedKey          \* Mapping from nodes to their owned private key

\* ------------------------------------------------------------------------
\* Block type enumeration
BlockType == {"genesis", "send", "receive", "open", "change"}

\* ------------------------------------------------------------------------
\* Record definition for a block.  Unused fields are set to sentinel values.
Block ==
    [ type           : BlockType,
      account        : PublicKey,
      prev           : Hash,
      amount         : Nat,
      dest           : PublicKey,
      source         : Hash,
      representative : PublicKey,
      sig            : PrivateKey ]

\* ------------------------------------------------------------------------
\* Helper: signing a block with a private key (the signature is simply the
\* private key in this abstract model)
SignBlock(priv, blk) ==
    [blk EXCEPT !.sig = priv]

\* ------------------------------------------------------------------------
\* Predicate that checks whether a block's signature matches the public key
\* that owns its account chain.
ValidSig(b) ==
    /\ b.sig \in PrivateKey
    /\ PrivateKeyToPublic[b.sig] = b.account

\* ------------------------------------------------------------------------
\* Variables
VARIABLES
    lastHash,        \* The most recent block hash that has been created
    ledger,          \* [Node -> [Hash -> Block]]  (local copy of the ledger)
    received,        \* [Node -> SUBSET Hash]      (blocks awaiting validation)
    blocksMap        \* [Hash -> Block]            (global repository of created blocks)

\* ------------------------------------------------------------------------
\* Initial state
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]
    /\ blocksMap = [h \in Hash |-> NoBlock]

\* ------------------------------------------------------------------------
\* Abstract hash calculation (overridden by CalculateHashImpl in the .cfg)
CalculateHash(d) == CalculateHashImpl(d)

\* ------------------------------------------------------------------------
\* Genesis block creation (can occur only once)
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E n \in Node :
         ( LET priv   == NodeOwnedKey[n],
               acct   == PrivateKeyToPublic[priv],
               blk    == SignBlock(priv,
                         [type           |-> "genesis",
                          account        |-> acct,
                          prev           |-> NoHash,
                          amount         |-> GenesisBalance,
                          dest           |-> NoHash,
                          source         |-> NoHash,
                          representative|-> acct,
                          sig            |-> priv]),
               h      == CalculateHash(blk)
           IN
               /\ h \in Hash
               /\ blocksMap' = [blocksMap EXCEPT ![h] = blk]
               /\ ledger'   = [n2 \in Node |-> [h2 \in Hash |-> IF h2 = h THEN blk ELSE ledger[n2][h2]]]
               /\ received' = received
               /\ lastHash' = h)

\* ------------------------------------------------------------------------
\* Helper to obtain the public key of a node
NodePubKey(n) == PrivateKeyToPublic[NodeOwnedKey[n]]

\* ------------------------------------------------------------------------
\* Create a send block (reduces sender's balance)
CreateSend ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node :
         ( LET priv == NodeOwnedKey[n],
               acct == PrivateKeyToPublic[priv],
               bal  == Balance(acct)
           IN
               /\ \E amt \in 0..bal :
                     /\ \E dest \in PublicKey \ {acct} :
                           LET blk == SignBlock(priv,
                                      [type           |-> "send",
                                       account        |-> acct,
                                       prev           |-> lastHash,
                                       amount         |-> amt,
                                       dest           |-> dest,
                                       source         |-> NoHash,
                                       representative|-> acct,
                                       sig            |-> priv]),
                               h   == CalculateHash(blk)
                           IN
                               /\ h \in Hash
                               /\ blocksMap' = [blocksMap EXCEPT ![h] = blk]
                               /\ received' = [n2 \in Node |-> received[n2] \cup {h}]
                               /\ ledger'   = ledger
                               /\ lastHash' = h))

\* ------------------------------------------------------------------------
\* Create an open block (first block of a new account)
CreateOpen ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node :
         ( LET priv == NodeOwnedKey[n],
               acct == PrivateKeyToPublic[priv]
           IN
               /\ \E src \in Hash :
                     LET srcBlk == blocksMap[src]
                     IN
                         /\ srcBlk.type = "open"? FALSE \* ensure we don't reuse an open block
                         /\ srcBlk.type = "send"
                         /\ srcBlk.dest = acct
                         LET blk == SignBlock(priv,
                                    [type           |-> "open",
                                     account        |-> acct,
                                     prev           |-> NoHash,
                                     amount         |-> srcBlk.amount,
                                     dest           |-> NoHash,
                                     source         |-> src,
                                     representative|-> acct,
                                     sig            |-> priv]),
                             h   == CalculateHash(blk)
                         IN
                             /\ h \in Hash
                             /\ blocksMap' = [blocksMap EXCEPT ![h] = blk]
                             /\ received' = [n2 \in Node |-> received[n2] \cup {h}]
                             /\ ledger'   = ledger
                             /\ lastHash' = h))

\* ------------------------------------------------------------------------
\* Create a receive block (adds received amount to balance)
CreateReceive ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node :
         ( LET priv == NodeOwnedKey[n],
               acct == PrivateKeyToPublic[priv]
           IN
               /\ \E src \in Hash :
                     LET srcBlk == blocksMap[src]
                     IN
                         /\ srcBlk.type = "send"
                         /\ srcBlk.dest = acct
                         LET blk == SignBlock(priv,
                                    [type           |-> "receive",
                                     account        |-> acct,
                                     prev           |-> lastHash,
                                     amount         |-> srcBlk.amount,
                                     dest           |-> NoHash,
                                     source         |-> src,
                                     representative|-> acct,
                                     sig            |-> priv]),
                             h   == CalculateHash(blk)
                         IN
                             /\ h \in Hash
                             /\ blocksMap' = [blocksMap EXCEPT ![h] = blk]
                             /\ received' = [n2 \in Node |-> received[n2] \cup {h}]
                             /\ ledger'   = ledger
                             /\ lastHash' = h))

\* ------------------------------------------------------------------------
\* Create a change‑representative block
CreateChange ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node :
         ( LET priv   == NodeOwnedKey[n],
               acct   == PrivateKeyToPublic[priv],
               newRep == CHOOSE pk \in PublicKey : TRUE,
               blk    == SignBlock(priv,
                          [type           |-> "change",
                           account        |-> acct,
                           prev           |-> lastHash,
                           amount         |-> 0,
                           dest           |-> NoHash,
                           source         |-> NoHash,
                           representative|-> newRep,
                           sig            |-> priv]),
               h      == CalculateHash(blk)
           IN
               /\ h \in Hash
               /\ blocksMap' = [blocksMap EXCEPT ![h] = blk]
               /\ received' = [n2 \in Node |-> received[n2] \cup {h}]
               /\ ledger'   = ledger
               /\ lastHash' = h)

\* ------------------------------------------------------------------------
\* Process a received block at a node (validation and addition to the ledger)
ProcessReceived ==
    /\ \E n \in Node :
         \E h \in received[n] :
              LET blk == blocksMap[h]
              IN
                  /\ ValidSig(blk)               \* signature check
                  /\ ledger'   = [ledger EXCEPT ![n][h] = blk]
                  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
                  /\ blocksMap' = blocksMap
                  /\ lastHash' = lastHash

\* ------------------------------------------------------------------------
\* The overall Next relation
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessReceived

\* ------------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<lastHash, ledger, received, blocksMap>>

\* ------------------------------------------------------------------------
\* Abstract balance function (recursive definition omitted; kept abstract)
Balance(pub) == CHOOSE b \in Nat : TRUE

\* ------------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
    /\ (lastHash \in Hash) \/ (lastHash = NoHashVal)
    /\ ledger \in [Node -> [Hash -> Block]]
    /\ received \in [Node -> SUBSET Hash]
    /\ blocksMap \in [Hash -> Block]
    /\ PrivateKeyToPublic \in [PrivateKey -> PublicKey]
    /\ NodeOwnedKey \in [Node -> PrivateKey]

\* ------------------------------------------------------------------------
\* Safety invariant (all blocks stored in any ledger must have a valid signature)
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            (ledger[n][h] # NoBlock) => ValidSig(ledger[n][h])

\* ------------------------------------------------------------------------
\* Provide a concrete implementation for CalculateHashImpl (used by the
\* configuration file to replace CalculateHash).  Here we simply choose an
\* arbitrary hash value; the model checker will constrain it via the
\* constant definition.
CalculateHashImpl(d) == CHOOSE h \in Hash : TRUE

====