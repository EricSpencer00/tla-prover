---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Hash,               \* set of all possible block hashes
    NoHashVal,          \* sentinel value for a non‑existent hash (used in Init)
    PrivateKey,         \* set of private keys
    PublicKey,          \* set of public keys
    Node,               \* set of network nodes
    GenesisBalance,    \* total supply of the genesis account (Nat)
    NoBlockVal,         \* sentinel value for an empty/absent block
    CalculateHash,      \* abstract hash function (to be overridden by CalculateHashImpl)
    NoHash,             \* sentinel hash value meaning “no previous hash”
    NoBlock             \* sentinel block value (may be equal to NoBlockVal)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Block == [
    hash     : Hash,
    type     : {"genesis", "send", "open", "receive", "change"},
    prev     : Hash,
    src      : PublicKey,    \* sender (for send/open/receive/change)
    dst      : PublicKey,    \* receiver (for send/open/receive)
    amount   : Nat,
    rep      : PublicKey,    \* representative (for change)
    signer   : PublicKey,    \* public key that signed the block
    signature: STRING        \* abstract signature
]

\* ----------------------------------------------------------------------
\* Abstract cryptographic primitives (treated as uninterpreted)
\* ----------------------------------------------------------------------
Sign(sk, data) == CHOOSE sig \in STRING : TRUE
VerifySignature(pk, data, sig) == TRUE

\* Mapping from private key to its public key (abstract, total)
PrivToPub == [sk \in PrivateKey |-> CHOOSE pk \in PublicKey : TRUE]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,   \* the hash of the most recently created block (or NoHash)
    ledger,     \* global ledger: maps every possible hash to a block or NoBlockVal
    received    \* per‑node set of blocks that have been broadcast but not yet processed

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ ledger = [h \in Hash |-> NoBlockVal]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
NoGenesisBlock ==
    ~(\E h \in Hash : ledger[h] # NoBlockVal /\ ledger[h].type = "genesis")

BlockOwnedBy(b) == b.signer

ValidBlock(b) ==
    /\ b.hash \in Hash
    /\ b.prev \in Hash
    /\ b.amount \in Nat
    /\ b.type \in {"genesis","send","open","receive","change"}
    /\ VerifySignature(b.signer, b, b.signature)

CanCreateSend(node, pk, amount, prevHash) ==
    /\ ledger[prevHash] # NoBlockVal
    /\ ledger[prevHash].signer = pk
    /\ amount <= GenesisBalance   \* (placeholder – real balance check omitted)

CanCreateOpen(node, pk, srcHash) ==
    /\ ledger[srcHash] # NoBlockVal
    /\ ledger[srcHash].type = "send"
    /\ ledger[srcHash].dst = pk
    /\ ~(\E h \in Hash : ledger[h] # NoBlockVal /\ ledger[h].type = "receive" /\ ledger[h].src = srcHash)

CanCreateReceive(node, pk, prevHash, srcHash) ==
    /\ ledger[prevHash] # NoBlockVal
    /\ ledger[prevHash].signer = pk
    /\ ledger[srcHash] # NoBlockVal
    /\ ledger[srcHash].type = "send"
    /\ ledger[srcHash].dst = pk
    /\ ~(\E h \in Hash : ledger[h] # NoBlockVal /\ ledger[h].type = "receive" /\ ledger[h].src = srcHash)

CanCreateChange(node, pk, prevHash) ==
    /\ ledger[prevHash] # NoBlockVal
    /\ ledger[prevHash].signer = pk

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ NoGenesisBlock
    /\ \E n \in Node, sk \in PrivateKey :
        LET pk == PrivToPub[sk],
            b  == [
                hash      |-> CalculateHash(<< "genesis", GenesisBalance >>, NoHash),
                type      |-> "genesis",
                prev      |-> NoHash,
                src       |-> pk,
                dst       |-> pk,
                amount    |-> GenesisBalance,
                rep       |-> pk,
                signer    |-> pk,
                signature |-> Sign(sk, << "genesis", GenesisBalance >>)
            ]
        IN
            /\ b.hash \in Hash
            /\ ValidBlock(b)
            /\ ledger' = [ledger EXCEPT ![b.hash] = b]
            /\ lastHash' = b.hash
            /\ received' = [node \in Node |-> received[node]]
            /\ UNCHANGED << >>

CreateSend ==
    /\ \E n \in Node, sk \in PrivateKey, amount \in Nat, prevHash \in Hash :
        LET pk == PrivToPub[sk],
            b  == [
                hash      |-> CalculateHash(<< "send", amount, prevHash >>, prevHash),
                type      |-> "send",
                prev      |-> prevHash,
                src       |-> pk,
                dst       |-> CHOOSE dst \in PublicKey : TRUE,
                amount    |-> amount,
                rep       |-> pk,
                signer    |-> pk,
                signature |-> Sign(sk, << "send", amount, prevHash >>)
            ]
        IN
            /\ CanCreateSend(n, pk, amount, prevHash)
            /\ b.hash \in Hash
            /\ ValidBlock(b)
            /\ ledger' = ledger
            /\ lastHash' = b.hash
            /\ received' = [node \in Node |-> received[node] \cup {b}]
            /\ UNCHANGED << >>

CreateOpen ==
    /\ \E n \in Node, sk \in PrivateKey, srcHash \in Hash :
        LET pk == PrivToPub[sk],
            b  == [
                hash      |-> CalculateHash(<< "open", srcHash >>, srcHash),
                type      |-> "open",
                prev      |-> srcHash,
                src       |-> pk,
                dst       |-> pk,
                amount    |-> ledger[srcHash].amount,
                rep       |-> pk,
                signer    |-> pk,
                signature |-> Sign(sk, << "open", srcHash >>)
            ]
        IN
            /\ CanCreateOpen(n, pk, srcHash)
            /\ b.hash \in Hash
            /\ ValidBlock(b)
            /\ ledger' = ledger
            /\ lastHash' = b.hash
            /\ received' = [node \in Node |-> received[node] \cup {b}]
            /\ UNCHANGED << >>

CreateReceive ==
    /\ \E n \in Node, sk \in PrivateKey, prevHash \in Hash, srcHash \in Hash :
        LET pk == PrivToPub[sk],
            b  == [
                hash      |-> CalculateHash(<< "receive", srcHash >>, prevHash),
                type      |-> "receive",
                prev      |-> prevHash,
                src       |-> srcHash,      \* reference to the send block
                dst       |-> pk,
                amount    |-> ledger[srcHash].amount,
                rep       |-> pk,
                signer    |-> pk,
                signature |-> Sign(sk, << "receive", srcHash >>)
            ]
        IN
            /\ CanCreateReceive(n, pk, prevHash, srcHash)
            /\ b.hash \in Hash
            /\ ValidBlock(b)
            /\ ledger' = ledger
            /\ lastHash' = b.hash
            /\ received' = [node \in Node |-> received[node] \cup {b}]
            /\ UNCHANGED << >>

CreateChange ==
    /\ \E n \in Node, sk \in PrivateKey, prevHash \in Hash, newRep \in PublicKey :
        LET pk == PrivToPub[sk],
            b  == [
                hash      |-> CalculateHash(<< "change", newRep >>, prevHash),
                type      |-> "change",
                prev      |-> prevHash,
                src       |-> pk,
                dst       |-> pk,
                amount    |-> 0,
                rep       |-> newRep,
                signer    |-> pk,
                signature |-> Sign(sk, << "change", newRep >>)
            ]
        IN
            /\ CanCreateChange(n, pk, prevHash)
            /\ b.hash \in Hash
            /\ ValidBlock(b)
            /\ ledger' = ledger
            /\ lastHash' = b.hash
            /\ received' = [node \in Node |-> received[node] \cup {b}]
            /\ UNCHANGED << >>

ProcessBlock ==
    /\ \E n \in Node, b \in received[n] :
        /\ ValidBlock(b)
        /\ ( ~(b.hash \in DOMAIN ledger) \/ ledger[b.hash] = NoBlockVal )
        /\ ledger' = [ledger EXCEPT ![b.hash] = b]
        /\ received' = [received EXCEPT ![n] = received[n] \setminus {b}]
        /\ UNCHANGED << lastHash >>

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \/ lastHash = NoHash
    /\ ledger \in [Hash -> (Block \cup {NoBlockVal})]
    /\ received \in [Node -> SUBSET Block]

SafetyInvariant ==
    \A h \in Hash :
        IF ledger[h] # NoBlockVal
        THEN VerifySignature(ledger[h].signer, ledger[h], ledger[h].signature)
        ELSE TRUE

\* ----------------------------------------------------------------------
\* Substituted implementation of CalculateHash (finite version)
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

====