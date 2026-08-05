---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS
    Hash,                   \* The set of all 256-bit Blake2b block hashes
    CalculateHash(_,_,_),   \* An action calculating the hash of a block
    PrivateKey,             \* All Ed25519 private keys
    PublicKey,              \* All Ed25519 public keys
    KeyPair,                \* The public key paired with each private key
    Node,                   \* The network's nodes
    GenesisBalance,         \* The total number of coins in the network
    Ownership               \* The private key owned by each node

VARIABLES
    lastHash,               \* The last calculated block hash
    distributedLedger,      \* The ledger of confirmed blocks
    received                \* Blocks received but not yet validated

ASSUME
    /\ \A data, oldHash, newHash :
        CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

\* Sign a hash with a private key
SignHash(hash, privateKey) ==
    [data |-> hash, signedWith |-> privateKey]

\* Validate a signature against a public key and a hash
ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[signature.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ signature.data = expectedHash

Signature == [data : Hash, signedWith : PrivateKey]
NoBlock == CHOOSE b \in Signature : b \notin Signature
NoHash == CHOOSE h \in Hash : h \notin Hash

Ledger == [Hash -> Signature \cup {NoBlock}]

GenesisBlockExists == lastHash # NoHash

\* Account balance is a natural number
AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type |-> "genesis", account |-> PublicKey, balance |-> {GenesisBalance}]

SendBlock ==
    [previous |-> Hash, balance |-> AccountBalance, destination |-> PublicKey, type |-> "send"]

OpenBlock ==
    [account |-> PublicKey, source |-> Hash, rep |-> PublicKey, type |-> "open"]

ReceiveBlock ==
    [previous |-> Hash, source |-> Hash, type |-> "receive"]

ChangeRepBlock ==
    [previous |-> Hash, rep |-> PublicKey, type |-> "change"]

Block == GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock

SignedBlock == [block : Block, signature : Signature]

\* Recursive block property: the public key of the account that created a block
RECURSIVE PublicKeyOf(_, _)
PublicKeyOf(ledger, blockHash) ==
    LET signedBlock == ledger[blockHash] IN
    IF signedBlock.block.type \in {"genesis", "open"}
    THEN signedBlock.block.account
    ELSE PublicKeyOf(ledger, signedBlock.block.previous)

\* The top block in an account's chain
TopBlock(ledger, publicKey) ==
    CHOOSE hash \in Hash :
        /\ ledger[hash] # NoBlock
        /\ PublicKeyOf(ledger, hash) = publicKey
        /\ \A otherHash \in Hash :
            ledger[otherHash] # NoBlock
            /\ ledger[otherHash].block.type \in {"send", "receive", "change"}
            /\ ledger[otherHash].block.previous # hash

\* The balance of an account at a block
RECURSIVE BalanceAt(_)
BalanceAt(ledger, hash) ==
    LET block == ledger[hash].block IN
    CASE block.type = "open" -> ValueOfSendBlock(ledger, block.source)
    [] block.type = "send" -> block.balance
    [] block.type = "receive" ->
        BalanceAt(ledger, block.previous)
        + ValueOfSendBlock(ledger, block.source)
    [] block.type = "change" -> BalanceAt(ledger, block.previous)
    [] block.type = "genesis" -> block.balance

\* The value sent by a send block
RECURSIVE ValueOfSendBlock(_, _)
ValueOfSendBlock(ledger, hash) ==
    LET block == ledger[hash].block IN
    BalanceAt(ledger, block.previous) - block.balance

\* Cryptographic integrity: each ledger entry is a valid signature of its hash
CryptographicInvariant ==
    /\ \A node \in Node :
        \A hash \in Hash :
            ledger[hash] # NoBlock => ValidateSignature(
                ledger[hash].signature,
                PublicKeyOf(ledger, hash),
                hash)
    /\ lastHash # NoHash

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(privateKey) ==
    LET publicKey == KeyPair[privateKey] IN
    /\ ~GenesisBlockExists
    /\ CalculateHash(GenesisBlock, lastHash, lastHash')
    /\ distributedLedger' =
        [n \in Node |->
            [distributedLedger[n] EXCEPT ![lastHash'] =
                [block |-> GenesisBlock, signature |-> SignHash(lastHash', privateKey)]]]
    /\ UNCHANGED received

\* Top-level action
Next ==
    \/ \E k \in PrivateKey : CreateGenesisBlock(k)
    \/ UNCHANGED <<lastHash, distributedLedger, received>>

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

THEOREM Safety == Spec => CryptographicInvariant

====