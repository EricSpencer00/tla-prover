---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS
    Hash, CalculateHash(_,_,_), PrivateKey, PublicKey,
    KeyPair, Node, GenesisBalance, Ownership

ASSUME
    /\ \A d, o, n : CalculateHash(d, o, n) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

VARIABLES
    lastHash, distributedLedger, received

NoHash == CHOOSE h \in Hash : TRUE
NoBlock == CHOOSE b \in [Hash -> [type : {"placeholder"}] \cup {[type : {"genesis", "open", "send", "receive", "change"}]}] : TRUE

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> [Hash -> {NoBlock} \cup [type : {"genesis", "open", "send", "receive", "change"}]]
    /\ received \in [Node -> SUBSET {NoBlock}]

\* A new block must be signed by the source account's private key.
SignHash(h, k) == [hash |-> h, signedBy |-> k]

Spec ==
    /\ \E k \in PrivateKey, h \in Hash : CalculateHash(k, NoHash, h)
    /\ \E k \in PrivateKey, h \in Hash :
        /\ lastHash = NoHash
        /\ KeyPair[k] \in PublicKey
        /\ lastHash' = h
        /\ UNCHANGED <<distributedLedger, received>>
    /\ UNCHANGED <<lastHash, distributedLedger, received>>

====