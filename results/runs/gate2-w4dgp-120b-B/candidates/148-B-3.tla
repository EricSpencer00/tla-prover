---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS
    NoHash,
    CalculateHash(_,_,_),
    PrivateKey,
    PublicKey,
    KeyPair,
    Node,
    GenesisBalance,
    Ownership

VARIABLES
    lastHash,
    distributedLedger,
    received

ASSUME
    /\ \A data, oldHash, newHash :
        /\ CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

\* Ed25519 signature: the hash and the private key that signed it.
Signature ==
    [data       : NoHash,
    signedWith  : PrivateKey]

\* The signature is validated against the account's public key and the hash.
ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[signature.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ signature.data = expectedHash

SignHash(hash, privateKey) ==
    [data       |-> hash,
    signedWith  |-> privateKey]

\* The hash and block fields are stored in a nested record: the outer map
\* indexes the block hash, which maps to a record holding the block and
\* the signature that produced that hash.
Ledger == [NoHash -> [block : NoHash, signature : Signature \cup {NoHash}]]

\* The hash field is a record, so a NoHash value is not a record, and the
\* lexical "block" field selector is not available on it. That's why we
\* always check for NoHash before selecting the block field.
\* Subtracting a set from a bag removes the bag's members in the set.
NoBlock == [block |-> NoHash, signature |-> NoHash]
LedgerExcluding(S) == [h \in NoHash |-> IF h \in S THEN NoBlock ELSE Ledger[h]]

TypeOK ==
    /\ lastHash \in NoHash
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET [block : NoHash, signature : Signature]]

\* The ledger is filled only by blocks that are cryptographically valid.
\* The account for any block is derived from the block's ancestry, not
\* from the signature's signedWith field.
CryptographicOK ==
    /\ \A node \in Node :
        LET ledger == distributedLedger[node] IN
        \A hash \in NoHash :
            LET record == ledger[hash] IN
            record.block /= NoHash =>
                ValidateSignature(record.signature,
                    ledger[hash].block,
                    hash)
    /\ \A node \in Node :
        \A block \in received[node] :
            LET h == block.block IN
            block.signature.signedWith = Ownership[node]
            /\ ~\E node2 \in Node : h \in LedgerExcluding({NoHash})[node2]

\* A block whose hash has already been recorded is never reprocessed.
\* Past the genesis block, every block adds at least one unit of balance.
NoReprocessing == \A node \in Node : ledger[hash].block = NoHash

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> Ledger]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(node, privateKey) ==
    /\ lastHash = NoHash
    /\ lastHash' = privateKey
    /\ distributedLedger' = [distributedLedger EXCEPT ![node] =
        [h \in NoHash |-> IF h = privateKey
            THEN [block |-> privateKey,
                signature |-> SignHash(privateKey, privateKey)]
            ELSE Ledger[h]]]
    /\ UNCHANGED received

Next ==
    \/ \E node \in Node, privateKey \in PrivateKey : CreateGenesisBlock(node, privateKey)

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

\* No state in the reachable state space should violate either invariant.
THEOREM NoInvariantViolation == Spec => TypeOK /\ CryptographicOK /\ NoReprocessing
====