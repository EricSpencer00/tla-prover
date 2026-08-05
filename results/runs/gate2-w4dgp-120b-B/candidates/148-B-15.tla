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
    lastHash,               \* The last calculated block hash
    distributedLedger,      \* The distributed ledger of confirmed blocks
    received                \* The blocks received but not yet validated

ASSUME
    /\ \A data, oldHash, newHash :
        /\ CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

\* Cryptographic signatures: sign a hash and validate against a public key.
SignHash(hash, privateKey) ==
    [data |-> hash, signedWith |-> privateKey]

ValidateSignature(sig, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[sig.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ sig.data = expectedHash

Signature == [data : Hash, signedWith : PrivateKey]

\* Blocks: genesis, send, open, receive, and rep-change.
GenesisBlock ==
    [type |-> "genesis", account |-> "gpub", balance |-> GenesisBalance]

SendBlock ==
    [previous : Hash, balance : 0 .. GenesisBalance, destination : PublicKey,
        type |-> "send"]

OpenBlock ==
    [account : PublicKey, source : Hash, rep : PublicKey, type |-> "open"]

ReceiveBlock ==
    [previous : Hash, source : Hash, type |-> "receive"]

ChangeRepBlock ==
    [previous : Hash, rep : PublicKey, type |-> "change"]

Block == GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock
            \cup ChangeRepBlock

SignedBlock == [block : Block, signature : Signature]

NoBlock == CHOOSE b \notin SignedBlock
NoHash == CHOOSE h \notin Hash

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

\* Account balance is the sum of all send-transfer values ending at the
\* latest block in an account's chain; no "minting" is permitted beyond the
\* genesis balance.
RECURSIVE BalanceAt(_)
BalanceAt(ledger, hash) ==
    LET signedBlock == ledger[hash] IN
    LET block == signedBlock.block IN
    CASE block.type = "open" ->
            BalanceAt(ledger, block.source)
        [] block.type = "send" -> block.balance
        [] block.type = "receive" ->
            BalanceAt(ledger, block.previous)
                + BalanceAt(ledger, block.source)
        [] block.type = "change" -> BalanceAt(ledger, block.previous)
        [] block.type = "genesis" -> block.balance

RECURSIVE PublicKeyOf(_,_)
PublicKeyOf(ledger, hash) ==
    LET signedBlock == ledger[hash] IN
    LET block == signedBlock.block IN
    IF block.type \in {"genesis", "open"}
    THEN block.account
    ELSE PublicKeyOf(ledger, block.previous)

RECURSIVE ValueOfSendBlock(_,_)
ValueOfSendBlock(ledger, hash) ==
    LET signedBlock == ledger[hash] IN
    LET block == signedBlock.block IN
    BalanceAt(ledger, block.previous) - block.balance

GenesisBlockExists == lastHash # NoHash

\* An account's chain is the latest block in it, the block whose hash is
\* referenced by no other block yet.
RECURSIVE TopBlock(_, _)
TopBlock(ledger, publicKey) ==
    CHOOSE hash \in Hash :
        LET signedBlock == ledger[hash] IN
        signedBlock # NoBlock /\ PublicKeyOf(ledger, hash) = publicKey
            /\ ~\E otherHash \in Hash :
                LET otherSignedBlock == ledger[otherHash] IN
                otherSignedBlock # NoBlock
                    /\ otherSignedBlock.block.type \in {"send", "receive", "change"}
                    /\ otherSignedBlock.block.previous = hash

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptographicOK ==
    /\ \A node \in Node :
        LET ledger == distributedLedger[node] IN
        \A hash \in Hash :
            LET signedBlock == ledger[hash] IN
            signedBlock # NoBlock =>
                LET publicKey == PublicKeyOf(ledger, hash) IN
                ValidateSignature(signedBlock.signature, publicKey, hash)

BalanceOK ==
    /\ \A node \in Node :
        LET ledger == distributedLedger[node] IN
        IF GenesisBlockExists
        THEN LET topBlocks == {TopBlock(ledger, a) : a \in PublicKey}
                 totalBalances == SumBag(
                        BagOfAll(BalanceAt(ledger), SetToBag(topBlocks))) IN
            totalBalances <= GenesisBalance
        ELSE TRUE

Spec ==
    /\ TRUE
    /\ [][TypeOK /\ CryptographicOK /\ BalanceOK]_<<lastHash, distributedLedger, received>>

====