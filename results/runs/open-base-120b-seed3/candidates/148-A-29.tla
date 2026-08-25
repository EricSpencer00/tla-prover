---- MODULE Nano ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Hash,          \* Set of all possible block hashes
    NoHashVal,    \* Sentinel value meaning “no hash”
    PrivateKey,   \* Set of private keys
    PublicKey,    \* Set of public keys
    Node,         \* Set of network nodes
    GenesisBalance, \* Total supply of coins (a natural number)
    NoBlockVal,   \* Sentinel value meaning “no block”
    CalculateHash, \* Abstract hash operator (overridden in the .cfg)
    NoHash,       \* Alias for NoHashVal used in records
    NoBlock       \* Alias for NoBlockVal used in records

\* ----------------------------------------------------------------------
\* Additional constants that are useful for the model (they may be
\* supplied in the configuration file as well).
\* ----------------------------------------------------------------------
CONSTANT PrivateToPublic \* Mapping PrivateKey -> PublicKey
CONSTANT OwnerKey        \* Mapping Node -> PrivateKey
CONSTANT GenesisAccount  \* Public key of the genesis account

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,    \* The hash of the most recently created block (or NoHashVal)
    ledger,      \* [Node -> [Hash -> BlockOrNoBlock]]
    received,    \* [Node -> SUBSET Hash] – blocks known but not yet processed
    Blocks       \* Global mapping Hash -> Block (or NoBlockVal)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Block == [
    type       : {"genesis", "send", "open", "receive", "change"},
    creator    : PublicKey,
    prev       : Hash,
    amount     : Nat,
    recipient  : PublicKey,
    source     : Hash,          \* For “receive” and “open” blocks
    signature  : STRING
]

BlockOrNoBlock == Block \cup {NoBlockVal}

\* ----------------------------------------------------------------------
\* Helper operators (abstract / nondeterministic where appropriate)
\* ----------------------------------------------------------------------
CalculateHashImpl(b, p) == 
    CHOOSE h \in Hash : TRUE     \* a nondeterministic hash in the finite set

Sign(pub, msg) == 
    "sig_" \o pub \o "_" \o msg   \* abstract signature representation

Balance(node, pub) == 
    CHOOSE b \in Nat : TRUE       \* abstract balance (constrained later)

IsValidSignature(blk) == 
    blk.signature = Sign(blk.creator, blk.type)

PrevExists(node, h) == 
    /\ h = NoHash
       \/ \E h2 \in Hash : ledger[node][h2] # NoBlockVal
                              /\ h2 = h

Validate(blk, node) ==
    /\ IsValidSignature(blk)
    /\ IF blk.type = "genesis" THEN TRUE
       ELSE IF blk.type = "send" THEN
            /\ blk.amount <= Balance(node, blk.creator)
            /\ PrevExists(node, blk.prev)
       ELSE IF blk.type = "open" THEN
            /\ blk.prev = NoHash
            /\ blk.source # NoHash
            /\ \E s \in Hash :
                 Blocks[s].type = "send"
                 /\ Blocks[s].recipient = blk.creator
                 /\ Blocks[s].amount = blk.amount
            /\ PrevExists(node, blk.prev)
       ELSE IF blk.type = "receive" THEN
            /\ blk.prev # NoHash
            /\ blk.source # NoHash
            /\ \E s \in Hash :
                 Blocks[s].type = "send"
                 /\ Blocks[s].recipient = blk.creator
                 /\ Blocks[s].amount = blk.amount
            /\ PrevExists(node, blk.prev)
       ELSE IF blk.type = "change" THEN
            /\ blk.prev # NoHash
            /\ PrevExists(node, blk.prev)
       ELSE FALSE

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledger   = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]
    /\ Blocks   = [h \in Hash |-> NoBlockVal]

\* ----------------------------------------------------------------------
\* Block‑creation actions
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E pk \in PrivateKey :
        LET pub == PrivateToPublic[pk] IN
        LET blk == [
                type       |-> "genesis",
                creator    |-> pub,
                prev       |-> NoHash,
                amount     |-> GenesisBalance,
                recipient  |-> NoHash,
                source     |-> NoHash,
                signature  |-> Sign(pub, "genesis")
            ] IN
        LET newHash == CalculateHashImpl(blk, NoHash) IN
        /\ newHash \in Hash
        /\ Blocks'   = [Blocks EXCEPT ![newHash] = blk]
        /\ lastHash' = newHash
        /\ ledger'   = ledger
        /\ received' = [n \in Node |-> received[n] \cup {newHash}]
        /\ UNCHANGED << >>

CreateSend ==
    /\ \E n \in Node :
        LET pk == OwnerKey[n] IN
        LET pub == PrivateToPublic[pk] IN
        \E amt \in Nat :
            \E rec \in PublicKey :
                /\ amt <= Balance(n, pub)
                LET blk == [
                        type       |-> "send",
                        creator    |-> pub,
                        prev       |-> lastHash,
                        amount     |-> amt,
                        recipient  |-> rec,
                        source     |-> NoHash,
                        signature  |-> Sign(pub, "send")
                    ] IN
                LET newHash == CalculateHashImpl(blk, lastHash) IN
                /\ newHash \in Hash
                /\ Blocks'   = [Blocks EXCEPT ![newHash] = blk]
                /\ lastHash' = newHash
                /\ ledger'   = ledger
                /\ received' = [m \in Node |-> received[m] \cup {newHash}]
                /\ UNCHANGED << >>

CreateOpen ==
    /\ \E n \in Node :
        LET pk == OwnerKey[n] IN
        LET pub == PrivateToPublic[pk] IN
        \E src \in Hash :
            /\ Blocks[src].type = "send"
            /\ Blocks[src].recipient = pub
            LET blk == [
                    type       |-> "open",
                    creator    |-> pub,
                    prev       |-> NoHash,
                    amount     |-> Blocks[src].amount,
                    recipient  |-> NoHash,
                    source     |-> src,
                    signature  |-> Sign(pub, "open")
                ] IN
                LET newHash == CalculateHashImpl(blk, NoHash) IN
                /\ newHash \in Hash
                /\ Blocks'   = [Blocks EXCEPT ![newHash] = blk]
                /\ lastHash' = newHash
                /\ ledger'   = ledger
                /\ received' = [m \in Node |-> received[m] \cup {newHash}]
                /\ UNCHANGED << >>

CreateReceive ==
    /\ \E n \in Node :
        LET pk == OwnerKey[n] IN
        LET pub == PrivateToPublic[pk] IN
        \E src \in Hash :
            /\ Blocks[src].type = "send"
            /\ Blocks[src].recipient = pub
            \E srcPrev \in Hash :
                /\ Blocks[srcPrev].type = "send"
                /\ srcPrev # src   \* ensure distinct send blocks (simplified)
                LET blk == [
                        type       |-> "receive",
                        creator    |-> pub,
                        prev       |-> lastHash,
                        amount     |-> Blocks[src].amount,
                        recipient  |-> NoHash,
                        source     |-> src,
                        signature  |-> Sign(pub, "receive")
                    ] IN
                LET newHash == CalculateHashImpl(blk, lastHash) IN
                /\ newHash \in Hash
                /\ Blocks'   = [Blocks EXCEPT ![newHash] = blk]
                /\ lastHash' = newHash
                /\ ledger'   = ledger
                /\ received' = [m \in Node |-> received[m] \cup {newHash}]
                /\ UNCHANGED << >>

CreateChange ==
    /\ \E n \in Node :
        LET pk == OwnerKey[n] IN
        LET pub == PrivateToPublic[pk] IN
        LET blk == [
                type       |-> "change",
                creator    |-> pub,
                prev       |-> lastHash,
                amount     |-> 0,
                recipient  |-> NoHash,
                source     |-> NoHash,
                signature  |-> Sign(pub, "change")
            ] IN
        LET newHash == CalculateHashImpl(blk, lastHash) IN
        /\ newHash \in Hash
        /\ Blocks'   = [Blocks EXCEPT ![newHash] = blk]
        /\ lastHash' = newHash
        /\ ledger'   = ledger
        /\ received' = [m \in Node |-> received[m] \cup {newHash}]
        /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Processing (validation) of a received block
\* ----------------------------------------------------------------------
ProcessBlock ==
    /\ \E n \in Node :
        /\ \E h \in received[n] :
            LET blk == Blocks[h] IN
            /\ Validate(blk, n)
            /\ ledger'   = [ledger EXCEPT ![n][h] = blk]
            /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
            /\ UNCHANGED << lastHash, Blocks >>

\* ----------------------------------------------------------------------
\* Next‑state relation
\* ----------------------------------------------------------------------
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
Spec == Init /\ [][Next]_<< lastHash, ledger, received, Blocks >>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \/ lastHash = NoHashVal
    /\ ledger \in [Node -> [Hash -> BlockOrNoBlock]]
    /\ received \in [Node -> SUBSET Hash]
    /\ Blocks \in [Hash -> BlockOrNoBlock]

SafetyInvariant ==
    /\ \A n \in Node :
        \A h \in Hash :
            (ledger[n][h] # NoBlockVal) => IsValidSignature(ledger[n][h])

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\* ----------------------------------------------------------------------
THEOREM SpecIsSpec == Spec

====