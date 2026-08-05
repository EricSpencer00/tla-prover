---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS
    Hash,                   \* Blake2b block hashes
    CalculateHash(_,_,_),   \* Action that calculates the hash of a block
    PrivateKey,             \* Ed25519 private keys
    PublicKey,              \* Ed25519 public keys
    KeyPair,                \* Public key paired with each private key
    Node,                   \* Nodes in the network
    GenesisBalance,         \* Total number of coins in the network
    Ownership               \* Private key owned by each node

VARIABLES
    lastHash,               \* The last calculated block hash
    distributedLedger,      \* Confirmed blocks per node
    received                \* Blocks received but not yet validated

ASSUME
    /\ \A data, oldHash, newHash : CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

\* Ed25519-signature of a hash
SignHash(hash, privateKey) ==
    [data |-> hash, signedWith |-> privateKey]

ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[signature.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ signature.data = expectedHash

Signature == [data : Hash, signedWith : PrivateKey]
NoBlock == CHOOSE b : b \notin Signature
NoHash == CHOOSE h : h \notin Hash
Ledger == [Hash -> Signature \cup {NoBlock}]

GenesisBlock == [type |-> "genesis", account |-> PublicKey, balance |-> {GenesisBalance}]
SendBlock == [previous |-> Hash, balance : AccountBalance, destination : PublicKey, type |-> "send"]
OpenBlock == [account |-> PublicKey, source |-> Hash, rep |-> PublicKey, type |-> "open"]
ReceiveBlock == [previous |-> Hash, source |-> Hash, type |-> "receive"]
ChangeRepBlock == [previous |-> Hash, rep |-> PublicKey, type |-> "change"]
Block == GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock
SignedBlock == [block : Block, signature : Signature]

RECURSIVE PublicKeyOf(_, _)
PublicKeyOf(ledger, hash) ==
    LET block == ledger[hash].block IN
    IF block.type \in {"genesis", "open"}
    THEN block.account
    ELSE PublicKeyOf(ledger, block.previous)

RECURSIVE BalanceAt(_)
BalanceAt(ledger, hash) ==
    LET block == ledger[hash].block IN
    CASE block.type = "open" -> BalanceAt(ledger, block.source)
    [] block.type = "send" -> block.balance
    [] block.type = "receive" ->
        BalanceAt(ledger, block.previous) + BalanceAt(ledger, block.source)
    [] block.type = "change" -> BalanceAt(ledger, block.previous)
    [] block.type = "genesis" -> block.balance

GenesisBlockExists == lastHash # NoHash
IsAccountOpen(ledger, publicKey) ==
    \E hash \in Hash : ledger[hash] # NoBlock /\ ledger[hash].block.type \in {"genesis", "open"}
        /\ ledger[hash].block.account = publicKey

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptoOK ==
    \A node \in Node : \A hash \in Hash : LET s == distributedLedger[node][hash] IN
        (s # NoBlock => ValidateSignature(s.signature, PublicKeyOf(distributedLedger[node], hash), hash))

BalanceInvariant ==
    \A node \in Node :
        LET ledger == distributedLedger[node] IN
        LET accounts == {pk \in PublicKey : IsAccountOpen(ledger, pk)} IN
        LET topBlocks == {CHOOSE h \in Hash : ledger[h] # NoBlock /\ PublicKeyOf(ledger, h) = pk
                            /\ ~\E h2 \in Hash : ledger[h2] # NoBlock /\ ledger[h2].block.type \in {"send", "receive", "change"}
                                /\ ledger[h2].block.previous = h} FOR pk \in accounts IN
        LET accountBalances == BagOfAll(BalanceAt(ledger), SetToBag(topBlocks)) IN
        IF GenesisBlockExists THEN SumBag(accountBalances) <= GenesisBalance

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(privateKey) ==
    LET publicKey == KeyPair[privateKey] IN
    /\ ~GenesisBlockExists
    /\ CalculateHash([type |-> "genesis", account |-> publicKey, balance |-> GenesisBalance], lastHash, lastHash')
    /\ distributedLedger' = [n \in Node |-> [distributedLedger[n] EXCEPT ![lastHash'] = [block |-> [type |-> "genesis", account |-> publicKey, balance |-> GenesisBalance], signature |-> SignHash(lastHash', privateKey)]]]
    /\ UNCHANGED received

\* Actions for all other block types follow the same pattern: they
\* validate against their own ledger and never read from the live network.

Spec == Init /\ [][\E node \in Node : CreateGenesisBlock(Ownership[node]) \/ UNCHANGED <<lastHash, distributedLedger, received>>]_<<lastHash, distributedLedger, received>>

THEOREM Spec => TypeOK /\ CryptoOK

====