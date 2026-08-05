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

VARIABLES
    lastHash,
    distributedLedger,
    received

ASSUME
    /\ \A data, oldHash, newHash : CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

SignHash(hash, privateKey) ==
    [data |-> hash, signedWith |-> privateKey]

ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[signature.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ signature.data = expectedHash

Signature == [data : Hash, signedWith : PrivateKey]

NoBlock == CHOOSE b \in Block : b \notin Block
NoHash == CHOOSE h \in Hash : h \notin Hash

Ledger == [Hash -> Block \cup {NoBlock}]

GenesisBlockExists == lastHash /= NoHash

TopBlock(ledger, publicKey) ==
    CHOOSE hash \in Hash :
        LET b == ledger[hash] IN
        /\ b # NoBlock
        /\ b.account = publicKey
        /\ ~\E otherHash \in Hash :
            /\ ledger[otherHash] # NoBlock
            /\ ledger[otherHash].type \in {"send", "receive", "change"}
            /\ ledger[otherHash].previous = hash

RECURSIVE BalanceAt(_)
BalanceAt(ledger, hash) ==
    IF ledger[hash] = NoBlock THEN 0
    ELSE IF ledger[hash].type = "genesis" THEN ledger[hash].balance
    ELSE IF ledger[hash].type = "send" THEN ledger[hash].balance
    ELSE IF ledger[hash].type = "receive" THEN
        BalanceAt(ledger, ledger[hash].previous) + ledger[hash].balance
    ELSE BalanceAt(ledger, ledger[hash].previous)

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET Signature]

RECURSIVE SumBag(_)
SumBag(B) ==
    IF B = {} THEN 0
    ELSE LET e == CHOOSE x \in B : TRUE IN e + SumBag(B \ {e})

BalanceInvariant ==
    /\ \A node \in Node :
        LET ledger == distributedLedger[node] IN
        LET accounts == {b.account : b \in ledger} IN
        LET topBlocks == {TopBlock(ledger, a) : a \in accounts} IN
        LET balances == {BalanceAt(ledger, h) : h \in topBlocks} IN
        SumBag(balances) <= GenesisBalance

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(privateKey) ==
    LET publicKey == KeyPair[privateKey] IN
    /\ ~GenesisBlockExists
    /\ lastHash' = "genesisHash"
    /\ distributedLedger' = [n \in Node |->
        [distributedLedger[n] EXCEPT ![lastHash'] = [type |-> "genesis",
        account |-> publicKey, balance |-> GenesisBalance]]]
    /\ UNCHANGED received

CreateBlock(node) ==
    /\ lastHash' = "blockHash"
    /\ distributedLedger' = [distributedLedger EXCEPT ![node][lastHash']
        = [type |-> "send", previous |-> lastHash, balance |-> 1,
            destination |-> "dest"]]
    /\ UNCHANGED received

Spec == Init /\ [][CreateGenesisBlock(Ownership[n]) \/ CreateBlock(n)]_<<lastHash, distributedLedger, received>>

THEOREM Invariant == Spec => TypeInvariant /\ BalanceInvariant
====