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

\* Functions to sign hashes with a private key and validate signatures
\* against a public key
SignHash(hash, privateKey) == [data |-> hash, signedWith |-> privateKey]

ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[signature.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ signature.data = expectedHash

Signature == [data : Hash, signedWith : PrivateKey]

\* An open block is only valid if its source block exists and is a send
\* block to the account being opened
ValidateOpenBlock(ledger, block) ==
    /\ block.type = "open"
    /\ ledger[block.source] /= NoBlock
    /\ ledger[block.source].block.type = "send"
    \/ ledger[block.source].block.destination = block.account

ValidateSendBlock(ledger, block) ==
    /\ block.type = "send"
    /\ ledger[block.previous] /= NoBlock
    /\ block.balance <= BalanceAt(ledger, block.previous)

ValidateReceiveBlock(ledger, block) ==
    /\ block.type = "receive"
    /\ ledger[block.previous] /= NoBlock
    /\ ledger[block.source] /= NoBlock
    /\ ledger[block.source].block.type = "send"
    /\ ledger[block.source].block.destination
        = PublicKeyOf(ledger, block.previous)

ValidateChangeBlock(ledger, block) ==
    /\ block.type = "change"
    /\ ledger[block.previous] /= NoBlock

AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type |-> "genesis", account |-> CHOOSE k \in PublicKey : TRUE,
    balance |-> GenesisBalance]

GenesisBlockExists == lastHash /= NoHash

\* Does an account already have an open block in the ledger?
IsAccountOpen(ledger, publicKey) ==
    /\ \E hash \in Hash :
        LET signedBlock == ledger[hash] IN
        /\ signedBlock /= NoBlock
        /\ signedBlock.block.type \in {"genesis", "open"}
        /\ signedBlock.block.account = publicKey

NoBlock == CHOOSE b \notin Signature : TRUE
NoHash == CHOOSE h \notin Hash : TRUE

Ledger == [Hash -> Signature \cup {NoBlock}]
Block == GenesisBlock \cup [type : {"send","open","receive","change"},
    previous : Hash, source : Hash, account : PublicKey,
    destination : PublicKey, balance : AccountBalance, rep : PublicKey]

\* Recurse through the block lattice to find who a block belongs to
RECURSIVE PublicKeyOf(_,_)
PublicKeyOf(ledger, hash) ==
    LET signedBlock == ledger[hash] IN
    IF signedBlock.block.type \in {"genesis","open"}
    THEN signedBlock.block.account
    ELSE PublicKeyOf(ledger, signedBlock.block.previous)

\* Find the top of an account's block chain
TopBlock(ledger, publicKey) ==
    CHOOSE hash \in Hash :
        LET signedBlock == ledger[hash] IN
        /\ signedBlock /= NoBlock
        /\ PublicKeyOf(ledger, hash) = publicKey
        /\ ~\E otherHash \in Hash :
            LET otherSignedBlock == ledger[otherHash] IN
            /\ otherSignedBlock /= NoBlock
            /\ otherSignedBlock.block.type \in {"send","receive","change"}
            /\ otherSignedBlock.block.previous = hash

\* Find the balance at a block by recursion, so the recursion depth grows
\* with the length of the block chain rather than the state space size
RECURSIVE BalanceAt(_)
BalanceAt(ledger, hash) ==
    LET block == ledger[hash].block IN
    CASE block.type = "open" -> BalanceAt(ledger, block.source)
    [] block.type = "send" -> block.balance
    [] block.type = "receive" ->
        BalanceAt(ledger, block.previous)
        + BalanceAt(ledger, block.source)
    [] block.type = "change" -> BalanceAt(ledger, block.previous)
    [] block.type = "genesis" -> block.balance

\* Sum a bag of numbers without additional recursion depth
RECURSIVE SumBag(_)
SumBag(B) ==
    LET e == CHOOSE x \in B : TRUE IN e + SumBag(B \ {e})

\* Safety: no block is ever signed by a key other than the account it
\* belongs to, and the sum of every account balance never exceeds the
\* genesis balance
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET Signature]

CryptographicInvariant ==
    /\ \A node \in Node :
        LET ledger == distributedLedger[node] IN
        /\ \A hash \in Hash :
            LET signedBlock == ledger[hash] IN
            signedBlock /= NoBlock => /\ ValidateSignature(
                signedBlock, KeyPair[Ownership[node]], hash)

BalanceInvariant ==
    /\ \A node \in Node :
        LET
          ledger == distributedLedger[node]
          accounts == {k \in PublicKey : IsAccountOpen(ledger, k)}
          topBlocks == {TopBlock(ledger, k) : k \in accounts}
        IN SumBag({BalanceAt(ledger, h) : h \in topBlocks})
        <= GenesisBalance

SafetyInvariant == TypeInvariant /\ CryptographicInvariant

\* Genesis block is created only once
CreateGenesisBlock(privateKey) ==
    /\ ~GenesisBlockExists
    /\ CalculateHash(GenesisBlock, lastHash, lastHash')
    /\ LET signedGenesis ==
            [data |-> lastHash', signedWith |-> privateKey]
       IN distributedLedger' =
            [n \in Node |-> [distributedLedger[n] EXCEPT ![lastHash'] = signedGenesis]]
    /\ UNCHANGED received

\* Block creation is exposed as a single action per node, so the model
\* explores all the block types a node can write in one step instead of
\* spending a state on the node deciding what type to write next
CreateBlock(node) ==
    \/ \E block \in Block, key \in PrivateKey :
        /\ block.type = "open"
        /\ ValidateOpenBlock(distributedLedger[node], block)
        /\ CalculateHash(block, lastHash, lastHash')
        /\ received' =
            [n \in Node |-> IF n = node THEN received[n] \cup
                {[block |-> block, signature |-> SignHash(lastHash', key)]}
                ELSE received[n]]
        /\ UNCHANGED distributedLedger
    \/ \E block \in Block, key \in PrivateKey :
        /\ block.type = "send"
        /\ ValidateSendBlock(distributedLedger[node], block)
        /\ CalculateHash(block, lastHash, lastHash')
        /\ received' =
            [n \in Node |-> IF n = node THEN received[n] \cup
                {[block |-> block, signature |-> SignHash(lastHash', key)]}
                ELSE received[n]]
        /\ UNCHANGED distributedLedger
    \/ \E block \in Block, key \in PrivateKey :
        /\ block.type = "receive"
        /\ ValidateReceiveBlock(distributedLedger[node], block)
        /\ CalculateHash(block, lastHash, lastHash')
        /\ received' =
            [n \in Node |-> IF n = node THEN received[n] \cup
                {[block |-> block, signature |-> SignHash(lastHash', key)]}
                ELSE received[n]]
        /\ UNCHANGED distributedLedger
    \/ \E block \in Block, key \in PrivateKey :
        /\ block.type = "change"
        /\ ValidateChangeBlock(distributedLedger[node], block)
        /\ CalculateHash(block, lastHash, lastHash')
        /\ received' =
            [n \in Node |-> IF n = node THEN received[n] \cup
                {[block |-> block, signature |-> SignHash(lastHash', key)]}
                ELSE received[n]]
        /\ UNCHANGED distributedLedger

ProcessBlock(node) ==
    /\ \E block \in received[node] :
        LET ledger == distributedLedger[node] IN
        /\ \/ (block.block.type = "open"
                /\ ValidateOpenBlock(ledger, block.block)
                /\ ~IsAccountOpen(ledger, block.block.account))
            \/ (block.block.type = "send"
                /\ ValidateSendBlock(ledger, block.block))
            \/ (block.block.type = "receive"
                /\ ValidateReceiveBlock(ledger, block.block))
            \/ (block.block.type = "change"
                /\ ValidateChangeBlock(ledger, block.block))
        /\ CalculateHash(block.block, lastHash, lastHash')
        /\ ValidateSignature(block.signature, block.signature.signedWith, lastHash')
        /\ distributedLedger' =
            [distributedLedger EXCEPT ![node][lastHash'] = block]
        /\ received' = [received EXCEPT ![node] = @ \ {block}]

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

Next == \/ \E key \in PrivateKey : CreateGenesisBlock(key)
        \/ \E node \in Node : CreateBlock(node)
        \/ \E node \in Node : ProcessBlock(node)

Spec == /\ Init /\ [][Next]_<<lastHash, distributedLedger, received>>

THEOREM Safety == Spec => TypeInvariant /\ CryptographicInvariant

====