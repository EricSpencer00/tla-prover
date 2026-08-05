---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS
    Hash,
    CalculateHash(_,_,_),
    PrivateKey,
    PublicKey,
    KeyPair,
    Node,
    GenesisBalance,
    Ownership

ASSUME
    \A data, oldHash, newHash : CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

VARIABLES
    lastHash,
    distributedLedger,
    received

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> [Hash -> SignedBlock \cup {NoBlock}]]
    /\ received \in [Node -> SUBSET SignedBlock]

SignHash(hash, privateKey) ==
    [data |-> hash, signedWith |-> privateKey]

ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[signature.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ signature.data = expectedHash

Signature ==
    [data : Hash, signedWith : PrivateKey]

Block ==
    [type : {"genesis", "open", "send", "receive", "change"},
    account : PublicKey,
    balance : 0 .. GenesisBalance,
    destination : PublicKey,
    source : Hash,
    rep : PublicKey,
    previous : Hash]

SignedBlock ==
    [block : Block, signature : Signature]

NoBlock == CHOOSE b \in [block : Block, signature : Signature] : FALSE

NoHash == CHOOSE h \in Hash : FALSE

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

RECURSIVE PublicKeyOf(_, _)
PublicKeyOf(ledger, blockHash) ==
    LET signedBlock == ledger[blockHash] IN
    IF signedBlock.block.type \in {"genesis", "open"}
    THEN signedBlock.block.account
    ELSE PublicKeyOf(ledger, signedBlock.block.previous)

TopBlock(ledger, publicKey) ==
    CHOOSE hash \in Hash :
        LET signedBlock == ledger[hash] IN
        /\ signedBlock.block.type \in {"genesis", "open"}
        /\ PublicKeyOf(ledger, hash) = publicKey
        /\ ~\E otherHash \in Hash :
            ledger[otherHash].block.type \in {"send", "receive", "change"}
            /\ ledger[otherHash].block.previous = hash

RECURSIVE BalanceAt(_, _)
BalanceAt(ledger, hash) ==
    LET signedBlock == ledger[hash] IN
    CASE signedBlock.block.type = "open" -> ValueOfSendBlock(ledger, signedBlock.block.source)
    [] signedBlock.block.type = "send" -> signedBlock.block.balance
    [] signedBlock.block.type = "receive" ->
        BalanceAt(ledger, signedBlock.block.previous)
        + ValueOfSendBlock(ledger, signedBlock.block.source)
    [] signedBlock.block.type = "change" -> BalanceAt(ledger, signedBlock.block.previous)
    [] signedBlock.block.type = "genesis" -> signedBlock.block.balance
    [] OTHER -> 0

ValueOfSendBlock(ledger, hash) ==
    BalanceAt(ledger, ledger[hash].block.previous) - ledger[hash].block.balance

GenesisBlockExists == lastHash # NoHash

IsSendReceived(ledger, sourceHash) ==
    \E hash \in Hash :
        ledger[hash].block.type \in {"receive", "open"}
        /\ ledger[hash].block.source = sourceHash

CryptographicInvariant ==
    \A node \in Node :
        /\ \A hash \in Hash :
            ledger[hash] # NoBlock =>
                LET publicKey == PublicKeyOf(ledger, hash) IN
                ValidateSignature(ledger[hash].signature, publicKey, hash)

BalanceInvariant ==
    \A node \in Node :
        \E openAccounts \in SUBSET PublicKey :
            \E topHashes \in SUBSET Hash :
                /\ topHashes = {TopBlock(distributedLedger[node], a) : a \in openAccounts}
                /\ Sum({BalanceAt(distributedLedger[node], h) : h \in topHashes}) <= GenesisBalance

SafetyInvariant == CryptographicInvariant

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(privateKey) ==
    LET publicKey == KeyPair[privateKey] IN
    /\ ~GenesisBlockExists
    /\ \E lastHash' \in Hash :
        /\ CalculateHash([type |-> "genesis", account |-> publicKey, balance |-> GenesisBalance, destination |-> publicKey, source |-> NoHash, rep |-> publicKey, previous |-> NoHash], lastHash, lastHash')
        /\ distributedLedger' = [n \in Node |->
                [distributedLedger[n] EXCEPT ![lastHash'] = [block |-> [type |-> "genesis", account |-> publicKey, balance |-> GenesisBalance, destination |-> publicKey, source |-> NoHash, rep |-> publicKey, previous |-> NoHash], signature |-> SignHash(lastHash', privateKey)]]]
    /\ UNCHANGED received

ReceiveBlock ==
    LET publicKey == KeyPair[Ownership[CHOOSE n \in Node : TRUE]] IN
    \E hash \in Hash :
        /\ lastHash # NoHash
        /\ ~GenesisBlockExists
        /\ ~\E h \in Hash : distributedLedger[CHOOSE n \in Node : TRUE][h].block.type = "open"
        /\ CalculateHash([type |-> "open", account |-> publicKey, balance |-> GenesisBalance, destination |-> publicKey, source |-> hash, rep |-> publicKey, previous |-> NoHash], lastHash, lastHash)
        /\ distributedLedger' = [n \in Node |->
                [distributedLedger[n] EXCEPT ![lastHash] = [block |-> [type |-> "open", account |-> publicKey, balance |-> GenesisBalance, destination |-> publicKey, source |-> hash, rep |-> publicKey, previous |-> NoHash], signature |-> SignHash(lastHash, Ownership[n])]]]
        /\ UNCHANGED received

SendBlock ==
    LET publicKey == KeyPair[Ownership[CHOOSE n \in Node : TRUE]] IN
    \E hash \in Hash :
        /\ lastHash # NoHash
        /\ ~GenesisBlockExists
        /\ ~\E h \in Hash : distributedLedger[CHOOSE n \in Node : TRUE][h].block.type = "send"
        /\ \E amount \in 0 .. GenesisBalance :
            /\ CalculateHash([type |-> "send", account |-> publicKey, balance |-> amount, destination |-> publicKey, source |-> hash, rep |-> publicKey, previous |-> lastHash], lastHash, lastHash')
            /\ distributedLedger' = [n \in Node |->
                    [distributedLedger[n] EXCEPT ![lastHash'] = [block |-> [type |-> "send", account |-> publicKey, balance |-> amount, destination |-> publicKey, source |-> hash, rep |-> publicKey, previous |-> lastHash], signature |-> SignHash(lastHash', Ownership[n])]]]
        /\ UNCHANGED received

ReceiveReceive ==
    LET publicKey == KeyPair[Ownership[CHOOSE n \in Node : TRUE]] IN
    \E hash \in Hash :
        /\ lastHash # NoHash
        /\ ~GenesisBlockExists
        /\ ~\E h \in Hash : distributedLedger[CHOOSE n \in Node : TRUE][h].block.type = "receive"
        /\ ~IsSendReceived(distributedLedger[CHOOSE n \in Node : TRUE], hash)
        /\ CalculateHash([type |-> "receive", account |-> publicKey, balance |-> GenesisBalance, destination |-> publicKey, source |-> hash, rep |-> publicKey, previous |-> lastHash], lastHash, lastHash')
        /\ distributedLedger' = [n \in Node |->
                [distributedLedger[n] EXCEPT ![lastHash] = [block |-> [type |-> "receive", account |-> publicKey, balance |-> GenesisBalance, destination |-> publicKey, source |-> hash, rep |-> publicKey, previous |-> lastHash], signature |-> SignHash(lastHash, Ownership[n])]]]
        /\ UNCHANGED received

Next ==
    \/ \E privateKey \in PrivateKey : CreateGenesisBlock(privateKey)
    \/ ReceiveBlock
    \/ SendBlock
    \/ ReceiveReceive
    \/ \E node \in Node : received' = [received EXCEPT ![node] = {}]

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

=============================================================================