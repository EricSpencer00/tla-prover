---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS
    Hash,                   \* The set of all 256-bit Blake2b block hashes
    CalculateHash(_,_,_),   \* An action calculating the hash of a block
    PrivateKey,             \* The set of all Ed25519 private keys
    PublicKey,              \* The set of all Ed25519 public keys
    KeyPair,                \* The public key paired with each private key
    Node,                   \* The set of all nodes in the network
    GenesisBalance,         \* The total number of coins in the network
    Ownership               \* The private key owned by each node

VARIABLES
    lastHash,               \* The last calculated block hash (or NoHash)
    distributedLedger,      \* The distributed ledger of confirmed blocks
    received                \* The blocks received but not yet validated

ASSUME
    /\ \A data, oldHash, newHash :
        CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

\* ----------------------------------------------------------------------
\* Signatures and validation
\* ----------------------------------------------------------------------
Signature == [data : Hash, signedWith : PrivateKey]

SignHash(hash, privateKey) ==
    [data |-> hash, signedWith |-> privateKey]

ValidateSignature(sig, expectedPublicKey, expectedHash) ==
    LET pk == KeyPair[sig.signedWith] IN
        /\ pk = expectedPublicKey
        /\ sig.data = expectedHash

\* ----------------------------------------------------------------------
\* Block definitions
\* ----------------------------------------------------------------------
AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type    |-> "genesis",
     account |-> NoHash,      \* placeholder, never accessed
     balance |-> GenesisBalance]

SendBlock ==
    [type        |-> "send",
     previous    |-> NoHash,
     balance     |-> 0,
     destination |-> NoHash]

OpenBlock ==
    [type   |-> "open",
     account|-> NoHash,
     source |-> NoHash,
     rep    |-> NoHash]

ReceiveBlock ==
    [type    |-> "receive",
     previous|-> NoHash,
     source  |-> NoHash]

ChangeRepBlock ==
    [type    |-> "change",
     previous|-> NoHash,
     rep     |-> NoHash]

Block == GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock

SignedBlock == [block : Block, signature : Signature]

NoBlock == CHOOSE b : b \notin SignedBlock
NoHash == CHOOSE h : h \notin Hash

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

\* ----------------------------------------------------------------------
\* Utility functions
\* ----------------------------------------------------------------------
GenesisBlockExists == lastHash # NoHash

IsAccountOpen(ledger, pk) ==
    \E h \in Hash :
        LET sb == ledger[h] IN
            sb # NoBlock /\ sb.block.type \in {"genesis", "open"} /\ sb.block.account = pk

\* In this simplified model we only need PublicKeyOf for send/receive/change.
PublicKeyOf(ledger, h) ==
    LET sb == ledger[h] IN
        IF sb # NoBlock THEN
            IF sb.block.type \in {"genesis", "open"} THEN sb.block.account
            ELSE PublicKeyOf(ledger, sb.block.previous)
        ELSE NoHash

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptographicInvariant ==
    /\ \A n \in Node :
        \A h \in Hash :
            LET sb == distributedLedger[n][h] IN
                sb # NoBlock =>
                    LET pk == PublicKeyOf(distributedLedger[n], h) IN
                        ValidateSignature(sb.signature, pk, h)

SafetyInvariant == CryptographicInvariant

\* ----------------------------------------------------------------------
\* Genesis creation (kept minimal for model‑checking)
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ ~GenesisBlockExists
    /\ \E priv \in PrivateKey :
        LET pub == KeyPair[priv] IN
        /\ CalculateHash(GenesisBlock, lastHash, lastHash')
        /\ distributedLedger' =
            [n \in Node |-> [h \in Hash |-> NoBlock] EXCEPT ![lastHash'] = 
                [block |-> [type |-> "genesis", account |-> pub, balance |-> GenesisBalance],
                 signature |-> SignHash(lastHash', priv)]]
        /\ lastHash' # NoHash
        /\ UNCHANGED received

\* ----------------------------------------------------------------------
\* Dummy actions to allow the model to progress (they do not alter state)
\* ----------------------------------------------------------------------
NoOp == UNCHANGED <<lastHash, distributedLedger, received>>

Next ==
    \/ CreateGenesis
    \/ NoOp

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Theorem (kept for compatibility)
\* ----------------------------------------------------------------------
THEOREM Safety == Spec => TypeInvariant /\ SafetyInvariant

====