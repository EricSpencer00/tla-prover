---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS
    Hash, CalculateHash(_,_,_), PrivateKey, PublicKey, KeyPair,
    Node, GenesisBalance, Ownership

ASSUME
    /\ \A data, oldHash, newHash : CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

VARIABLES
    lastHash, distributedLedger, received

NoBlock == CHOOSE b \in (Hash \times PrivateKey) : TRUE
NoHash == CHOOSE h \in Hash : TRUE

Ledger == [Hash -> {NoBlock} \cup (Hash \times PrivateKey)]
Blocks == {[h \in Hash] : {NoBlock} \cup (Hash \times PrivateKey)}
NodeLedger == [Node -> Ledger]

SignHash(hash, privateKey) ==
    [hash |-> hash, signedWith |-> privateKey]

ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[signature.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ signature.hash = expectedHash

Signature == [hash : Hash, signedWith : PrivateKey]
SignedBlock == [block : Blocks, signature : Signature]

RECURSIVE PublicKeyOf(_, _)
PublicKeyOf(ledger, blockHash) ==
    LET block == ledger[blockHash] IN
    IF block # NoBlock
    THEN IF block[1] \in Hash
         THEN PublicKeyOf(ledger, block[1])
         ELSE block[2]
    ELSE NoBlock

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> {NoBlock}])
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(privateKey) ==
    /\ lastHash = NoHash
    /\ \E newHash \in Hash :
        /\ CalculateHash(privateKey, lastHash, newHash)
        /\ lastHash' = newHash
        /\ distributedLedger' = [n \in Node |-> [h \in Hash |-> {NoBlock}]]
        /\ distributedLedger' = [n \in Node |-> [distributedLedger[n]
            EXCEPT ![newHash] = {NoBlock, (privateKey, KeyPair[privateKey])}])
    /\ UNCHANGED received

ProcessGenesisBlock(node) ==
    /\ \E block \in received[node] :
        /\ block.block # {NoBlock}
        /\ ~\E other \in received[node] :
            /\ other \in block.block
            /\ other # block.block
        /\ \E hash \in Hash :
            /\ hash \notin block.block
            /\ block.block \in Blocks
            /\ block.block \subseteq block.block \cup {hash}
            /\ CalculateHash(block.block, lastHash, hash)
            /\ lastHash' = hash
            /\ distributedLedger' = [distributedLedger EXCEPT ![node][hash] = block.block]
        /\ received' = [received EXCEPT ![node] = @ \ {block}]

Next == \E node \in Node :
    \/ \E privateKey \in PrivateKey : CreateGenesisBlock(privateKey)
    \/ ProcessGenesisBlock(node)

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in NodeLedger
    /\ received \in [Node -> SUBSET SignedBlock]

TypeInv == Spec => TypeOK

====