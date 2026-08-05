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
    /\ \A data, oldHash, newHash : CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

VARIABLES
    lastHash,
    distributedLedger,
    received

vars == <<lastHash, distributedLedger, received>>

NoBlock == [block |-> CHOOSE b \in {} : TRUE, signature |-> CHOOSE s \in {} : TRUE]
NoHash == CHOOSE h \in {} : TRUE

Ledger == [Hash -> [block : [type : {"genesis", "open", "send", "receive", "change"},
                            account : PublicKey,
                            balance : Nat,
                            source : Hash,
                            destination : PublicKey,
                            rep : PublicKey],
                     signature : [data : Hash, signedWith : PrivateKey]] \cup {NoBlock}]

GenesisBlockExists == lastHash # NoHash

RECURSIVE SumBag(_)
SumBag(B) ==
    LET S == BagToSet(B) IN
    IF S = {} THEN 0
    ELSE LET e == CHOOSE x \in S : TRUE IN e + SumBag(B \ {e})

PublicKeyOf(ledger, blockHash) ==
    LET signedBlock == ledger[blockHash]
        block == signedBlock.block
    IN IF block.type \in {"genesis", "open"} THEN block.account
    ELSE PublicKeyOf(ledger, block.previous)

BalanceAt(ledger, hash) ==
    LET signedBlock == ledger[hash]
        block == signedBlock.block
    IN CASE block.type = "open" -> BalanceAt(ledger, block.source)
        [] block.type = "send" -> block.balance
        [] block.type = "receive" ->
            BalanceAt(ledger, block.previous) + BalanceAt(ledger, block.source)
        [] block.type = "change" -> BalanceAt(ledger, block.previous)
        [] block.type = "genesis" -> block.balance

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET Ledger]
    /\ \A node \in Node : HashDomain(distributedLedger[node]) = Hash

BalanceInvariant ==
    \A node \in Node :
        LET ledger == distributedLedger[node] IN
        LET openAccounts == {a \in PublicKey : \E h \in Hash : ledger[h].block.account = a} IN
        LET topBlocks == {CHOOSE hash \in Hash : ledger[hash].block.account = account : account \in openAccounts} IN
        LET ledgerBalanceAt(hash) == BalanceAt(ledger, hash) IN
        LET accountBalances == BagOfAll(ledgerBalanceAt, SetToBag(topBlocks)) IN
        SumBag(accountBalances) <= GenesisBalance

SignHash(hash, privateKey) == [data |-> hash, signedWith |-> privateKey]

ValidateSignature(sig, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[sig.signedWith] IN publicKey = expectedPublicKey /\ sig.data = expectedHash

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

Next ==
    \/ \E privateKey \in PrivateKey :
        /\ ~GenesisBlockExists
        /\ \E account \in PublicKey : account = KeyPair[privateKey]
        /\ \E newHash \in Hash :
            /\ CalculateHash([type |-> "genesis", account |-> account, balance |-> GenesisBalance], lastHash, newHash)
            /\ \E block \in Ledger :
                block[newHash] = [block |-> [type |-> "genesis",
                                             account |-> account,
                                             balance |-> GenesisBalance],
                                  signature |-> SignHash(newHash, privateKey)]
            /\ lastHash' = newHash
        /\ UNCHANGED <<distributedLedger, received>>
    \/ \E node \in Node, block \in Ledger, newHash \in Hash :
        /\ block \notin received[node]
        /\ CalculateHash(block.block, lastHash, newHash)
        /\ \E ledger \in [Name -> Ledger] :
            /\ ledger.node' = ledger.node \oplus [newHash |-> block]
            /\ lastHash' = newHash
            /\ block' = ledger
        /\ received' = [received EXCEPT ![node] = @ \cup {block}]
    \/ \E node \in Node, block \in received[node] :
        /\ \E newHash \in Hash :
            /\ CalculateHash(block.block, lastHash, newHash)
            /\ \E ledger \in [Name -> Ledger] :
                /\ ledger.node' = ledger.node \oplus [newHash |-> block]
                /\ lastHash' = newHash
                /\ block' = ledger
            /\ received' = [received EXCEPT ![node] = @ \ {block}]

Spec == Init /\ [][Next]_vars

====