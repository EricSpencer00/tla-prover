---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Hash,                \* The set of all possible block hashes
    NoHashVal,           \* A distinguished sentinel hash value meaning "no hash"
    PrivateKey,          \* Set of all private keys
    PublicKey,           \* Set of all public keys
    Node,                \* Set of all network nodes
    GenesisBalance,      \* Total amount of coins initially created
    NoBlockVal,          \* A distinguished sentinel for "no block"
    CalculateHash,       \* Abstract hash function: block data × previous hash → Hash
    NoHash,              \* Alias for NoHashVal (for readability)
    NoBlock              \* Alias for NoBlockVal (for readability)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
HashVal == Hash \cup {NoHash}
BlockId == { "genesis", "send", "open", "receive", "change" }
BlockType == {"genesis", "send", "open", "receive", "change"}

\* The structure of a block (record). Fields that are not applicable for a
\* particular block type are set to NoHash or NoBlock as appropriate.
Block == [
    type          : BlockType,
    owner         : PublicKey,          \* account that owns this chain
    prev          : HashVal,            \* previous block in the same chain
    src           : PublicKey,          \* for send/open/receive blocks
    dest          : PublicKey,          \* for send/open blocks
    amount        : Nat,                \* amount transferred (0 for non‑transfer blocks)
    signature     : PubKey,             \* public key that signed the block
    hash          : Hash                \* this block's hash
]

\* State variables
VARIABLES
    lastHash,            \* the most recent hash produced by the system
    ledger,              \* [node \in Node -> [hash \in Hash -> Block \cup {NoBlock}]]
    received,            \* [node \in Node -> SUBSET Hash]  blocks pending validation
    nodeKeyMap,          \* [node \in Node -> PrivateKey]  (owned private key of each node)
    priv2pub             \* [pk \in PrivateKey -> PublicKey] key‑pair mapping

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
HashOf(b) == b.hash

\* A block is valid if its hash matches the abstract CalculateHash applied to its
\* contents and its previous hash.
ValidHash(b) ==
    b.hash = CalculateHash(<<b.type, b.owner, b.prev, b.src, b.dest, b.amount, b.signature>>, b.prev)

\* Signature checks: the block’s signature field must equal the public key of the
\* account that owns the chain.
ValidSignature(b) ==
    b.signature = b.owner

\* Balance of an account is computed by walking its chain from the latest block
\* back to the genesis/open block.
\* For simplicity we treat a missing predecessor as zero balance.
RecBalance(acc, h) ==
    IF h = NoHash THEN 0
    ELSE
        LET b == ledger[Node][h] IN
        IF b = NoBlock THEN 0
        ELSE
            CASE b.type = "send"   -> RecBalance(acc, b.prev) - b.amount
                 [] b.type = "receive" -> RecBalance(acc, b.prev) + b.amount
                 [] b.type = "open"    -> b.amount
                 [] b.type = "change"  -> RecBalance(acc, b.prev)
                 [] b.type = "genesis" -> GenesisBalance
                 [] OTHER              -> 0

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]
    /\ nodeKeyMap \in [Node -> PrivateKey]
    /\ priv2pub \in [PrivateKey -> PublicKey]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E n \in Node :
        LET pk == nodeKeyMap[n] IN
        LET pub == priv2pub[pk] IN
        LET gBlock == [
            type      |-> "genesis",
            owner     |-> pub,
            prev      |-> NoHash,
            src       |-> NoHash,
            dest      |-> NoHash,
            amount    |-> GenesisBalance,
            signature |-> pub,
            hash      |-> NoHash \* will be replaced below
        ] IN
        /\ gBlock' = [gBlock EXCEPT !.hash = CalculateHash(<<gBlock.type, gBlock.owner,
                                gBlock.prev, gBlock.src, gBlock.dest,
                                gBlock.amount, gBlock.signature>>, NoHash)]
        /\ lastHash' = gBlock.hash
        /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![gBlock.hash] = gBlock]]
        /\ received' = [n \in Node |-> {}]
        /\ UNCHANGED <<nodeKeyMap, priv2pub>>

CreateSend ==
    /\ lastHash # NoHash
    /\ \E n \in Node :
        LET pk == nodeKeyMap[n] IN
        LET pub == priv2pub[pk] IN
        LET bal == RecBalance(pub, lastHash) IN
        \E amt \in Nat :
            /\ amt > 0
            /\ amt <= bal
            /\ \E destPub \in PublicKey :
                LET sBlock == [
                    type      |-> "send",
                    owner     |-> pub,
                    prev      |-> lastHash,
                    src       |-> pub,
                    dest      |-> destPub,
                    amount    |-> amt,
                    signature |-> pub,
                    hash      |-> NoHash
                ] IN
                /\ sBlock' = [sBlock EXCEPT !.hash = CalculateHash(<<sBlock.type, sBlock.owner,
                                    sBlock.prev, sBlock.src, sBlock.dest,
                                    sBlock.amount, sBlock.signature>>, lastHash)]
                /\ lastHash' = sBlock.hash
                /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![sBlock.hash] = sBlock]]
                /\ received' = [n \in Node |-> received[n] \cup {sBlock.hash}]
                /\ UNCHANGED <<nodeKeyMap, priv2pub>>

CreateOpen ==
    /\ \E n \in Node :
        LET pk == nodeKeyMap[n] IN
        LET pub == priv2pub[pk] IN
        \E sendHash \in Hash :
            LET sBlock == ledger[Node][sendHash] IN
            /\ sBlock.type = "send"
            /\ sBlock.dest = pub
            /\ \E oBlock == OpenBlockFor(pub, sBlock.amount) IN
                /\ oBlock' = [oBlock EXCEPT !.hash = CalculateHash(<<oBlock.type, oBlock.owner,
                                    oBlock.prev, oBlock.src, oBlock.dest,
                                    oBlock.amount, oBlock.signature>>, NoHash)]
                /\ lastHash' = oBlock.hash
                /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![oBlock.hash] = oBlock]]
                /\ received' = [n \in Node |-> received[n] \cup {oBlock.hash}]
                /\ UNCHANGED <<nodeKeyMap, priv2pub>>

OpenBlockFor(pub, amt) ==
    [
        type      |-> "open",
        owner     |-> pub,
        prev      |-> NoHash,
        src       |-> NoHash,
        dest      |-> pub,
        amount    |-> amt,
        signature |-> pub,
        hash      |-> NoHash
    ]

CreateReceive ==
    /\ lastHash # NoHash
    /\ \E n \in Node :
        LET pk == nodeKeyMap[n] IN
        LET pub == priv2pub[pk] IN
        \E recvHash \in Hash :
            LET rBlock == ledger[Node][recvHash] IN
            /\ rBlock.type = "receive"
            /\ \E sendHash \in Hash :
                LET sBlock == ledger[Node][sendHash] IN
                /\ sBlock.type = "send"
                /\ sBlock.dest = pub
                /\ sBlock.amount = rBlock.amount
                /\ rBlock.prev = lastHash
                /\ rBlock.owner = pub
                /\ rBlock.src = sBlock.owner
                /\ rBlock.dest = pub
                /\ rBlock' = [rBlock EXCEPT !.hash = CalculateHash(<<rBlock.type, rBlock.owner,
                                    rBlock.prev, rBlock.src, rBlock.dest,
                                    rBlock.amount, rBlock.signature>>, lastHash)]
                /\ lastHash' = rBlock.hash
                /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![rBlock.hash] = rBlock]]
                /\ received' = [n \in Node |-> received[n] \cup {rBlock.hash}]
                /\ UNCHANGED <<nodeKeyMap, priv2pub>>

CreateChange ==
    /\ lastHash # NoHash
    /\ \E n \in Node :
        LET pk == nodeKeyMap[n] IN
        LET pub == priv2pub[pk] IN
        LET cBlock == [
            type      |-> "change",
            owner     |-> pub,
            prev      |-> lastHash,
            src       |-> NoHash,
            dest      |-> NoHash,
            amount    |-> 0,
            signature |-> pub,
            hash      |-> NoHash
        ] IN
        /\ cBlock' = [cBlock EXCEPT !.hash = CalculateHash(<<cBlock.type, cBlock.owner,
                                cBlock.prev, cBlock.src, cBlock.dest,
                                cBlock.amount, cBlock.signature>>, lastHash)]
        /\ lastHash' = cBlock.hash
        /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![cBlock.hash] = cBlock]]
        /\ received' = [n \in Node |-> received[n] \cup {cBlock.hash}]
        /\ UNCHANGED <<nodeKeyMap, priv2pub>>

ProcessReceived ==
    /\ \E n \in Node :
        /\ \E h \in received[n] :
            LET b == ledger[n][h] IN
            /\ b # NoBlock
            /\ ValidHash(b)
            /\ ValidSignature(b)
            /\ ledger' = ledger
            /\ received' = [Node EXCEPT ![n] = received[n] \ {h}]
            /\ UNCHANGED <<lastHash, nodeKeyMap, priv2pub>>

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessReceived

\* ----------------------------------------------------------------------
\* Safety and type invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in HashVal
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]
    /\ nodeKeyMap \in [Node -> PrivateKey]
    /\ priv2pub \in [PrivateKey -> PublicKey]

SafetyInvariant ==
    /\ \A n \in Node :
          \A h \in Hash :
              LET b == ledger[n][h] IN
              b = NoBlock \/ (b \in Block /\ b.signature = b.owner)

Spec == Init /\ [][Next]_<<lastHash, ledger, received, nodeKeyMap, priv2pub>>

=============================================================================