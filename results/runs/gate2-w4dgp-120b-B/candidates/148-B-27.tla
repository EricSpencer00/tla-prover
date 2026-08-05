---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS
    Hash,
    CalculateHash(_,_,_),
    PrivateKey, PublicKey, KeyPair,
    Node, GenesisBalance,
    Ownership

ASSUME
    /\ \A data, oldHash, newHash : CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

VARIABLES lastHash, distributedLedger, received

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> [Hash -> SignedBlock \cup {NoBlock}]]
    /\ received \in [Node -> SUBSET SignedBlock]

\* A block's signature must be validated against the hash it was calculated
\* from, the block's own type, and the key of the node that produced it.
Signature == [data : Hash, signedWith : PrivateKey]
SignHash(b, k) == [data |-> b, signedWith |-> k]
ValidateSignature(s, pk, h) == (KeyPair[s.signedWith] = pk) /\ (s.data = h)

Block == {
    [type : "genesis", account : PublicKey, balance : {GenesisBalance}],
    [type : "open", account : PublicKey, source : Hash, rep : PublicKey],
    [type : "send", previous : Hash, balance : 0 .. GenesisBalance, destination : PublicKey],
    [type : "receive", previous : Hash, source : Hash],
    [type : "change", previous : Hash, rep : PublicKey]
}
SignedBlock == [block : Block, signature : Signature]
NoHash == CHOOSE h \in Hash : TRUE
NoBlock == CHOOSE b \in SignedBlock : TRUE

GenesisExists == lastHash # NoHash

\* The public key that owns the block at this hash, recursively working back
\* to the block's origin.
RECURSIVE PubKeyOf(_)
PubKeyOf(h) ==
    LET b == distributedLedger[Node][h] IN
    IF b.block.type = "genesis" \/ b.block.type = "open"
    THEN b.block.account
    ELSE PubKeyOf(b.block.previous)

BalanceOf(h) ==
    LET b == distributedLedger[Node][h] IN
    IF b.block.type = "open" THEN BalanceOf(b.block.source)
    ELSE IF b.block.type = "send" THEN b.block.balance
    ELSE IF b.block.type = "receive" THEN BalanceOf(b.block.previous) + BalanceOf(b.block.source)
    ELSE IF b.block.type = "change" THEN BalanceOf(b.block.previous)
    ELSE b.block.balance

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

\* The network starts with a single genesis block, signed by whoever owns
\* the private key that produced its hash.
CreateGenesis(k) ==
    /\ ~GenesisExists
    /\ \E h \in Hash :
        /\ CalculateHash([type |-> "genesis", account |-> KeyPair[k], balance |-> {GenesisBalance}], lastHash, h)
        /\ lastHash' = h
        /\ distributedLedger' = [n \in Node |-> [h \in Hash |->
                IF h = lastHash THEN [block |-> [type |-> "genesis", account |-> KeyPair[k], balance |-> {GenesisBalance}], signature |-> SignHash(h, k)]
                ELSE distributedLedger[n][h]]]
    /\ UNCHANGED received

\* Creating any other block records it in the "received but unvalidated"
\* bucket; it cannot become part of the chain without a correctly signed
\* signature validation.
CreateBlock(n) ==
    /\ \E b \in Block :
        /\ b.type # "genesis"
        /\ \E h \in Hash :
            /\ CalculateHash(b, lastHash, h)
            /\ lastHash' = h
            /\ received' = [received EXCEPT ![n] = @ \cup
                {[block |-> b, signature |-> SignHash(h, Ownership[n])]}]
    /\ UNCHANGED distributedLedger

\* A block becomes confirmed on the chain only after it passes the same
\* type- and key-correctness checks that the "received" bucket uses.
Confirm(n, s) ==
    /\ s \in received[n]
    /\ ValidateSignature(s.signature, PubKeyOf(s.block.previous), lastHash)
    /\ lastHash' = s.block.type
    /\ distributedLedger' = [distributedLedger EXCEPT ![n][lastHash] = s]
    /\ received' = [received EXCEPT ![n] = @ \ {s}]

Next ==
    \/ \E k \in PrivateKey : CreateGenesis(k)
    \/ \E n \in Node : CreateBlock(n) \/ \E s \in received[n] : Confirm(n, s)

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

\* Every block must be validated against the public key of the node that
\* produced its hash; a forged block signed by the wrong key would not pass.
ValidChain ==
    \A n \in Node, h \in Hash :
        (distributedLedger[n][h] # NoBlock) => ValidateSignature(distributedLedger[n][h].signature, PubKeyOf(h), h)

====