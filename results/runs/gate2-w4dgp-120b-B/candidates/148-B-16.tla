---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS
    Hash,                    \* 256-bit Blake2b hashes
    CalculateHash(_,_,_),    \* An action calculating a block hash
    PrivateKey,              \* Ed25519 private keys
    PublicKey,               \* Ed25519 public keys
    KeyPair,                 \* Public key paired with each private key
    Node,                    \* Nodes in the network
    GenesisBalance,          \* Total network coins
    Ownership                \* Private key owned by each node

VARIABLES
    lastHash,                \* Last calculated block hash
    distributedLedger,       \* Confirmed blocks per node
    received                 \* Blocks received but not validated

ASSUME
    /\ \A data, oldHash, newHash :
        CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

\* Signature captures the data it signs; there is no separate 'data' field.
Signature == [data : Hash, signedWith : PrivateKey]

SignHash(hash, privateKey) ==
    [data |-> hash, signedWith |-> privateKey]

ValidateSignature(sig, expPub, expHash) ==
    /\ KeyPair[sig.signedWith] = expPub
    /\ sig.data = expHash

NoBlock == CHOOSE b \in Block : TRUE
NoHash == CHOOSE h \in Hash : TRUE
Ledger == [Hash -> Block \cup {NoBlock}]

GenesisExists == lastHash # NoHash

Block ==
    [type : {"genesis", "open", "send", "receive", "change"},
     account : PublicKey, balance : 0..GenesisBalance,
     previous : Hash, source : Hash, destination : PublicKey,
     rep : PublicKey]

SignedBlock == [block : Block, signature : Signature]

\* Chain navigation is by hash, not by index, as a block can be replaced.
PublicKeyOf(ledger, h) ==
    IF ledger[h].type \in {"genesis", "open"}
    THEN ledger[h].account
    ELSE PublicKeyOf(ledger, ledger[h].previous)

TopBlock(ledger, pk) ==
    CHOOSE h \in Hash :
        /\ PublicKeyOf(ledger, h) = pk
        /\ ledger[h].type \in {"genesis", "open"}
        /\ ~\E g \in Hash :
            /\ ledger[g].type \in {"send", "receive", "change"}
            /\ ledger[g].previous = h

RECURSIVE BalanceAt(_)
BalanceAt(ledger, h) ==
    IF ledger[h].type = "open"
    THEN ledger[ledger[h].source].balance
    ELSE IF ledger[h].type = "send"
    THEN ledger[h].balance
    ELSE IF ledger[h].type = "receive"
    THEN BalanceAt(ledger, ledger[h].previous)
         + ledger[ledger[h].source].balance
    ELSE IF ledger[h].type = "change"
    THEN BalanceAt(ledger, ledger[h].previous)
    ELSE ledger[h].balance

RECURSIVE SumMultiset(_)
SumMultiset(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN x + SumMultiset(S \ {x})

BalanceInvariant ==
    \A n \in Node :
        LET open ==
            {PublicKeyOf(distributedLedger[n], h) : h \in Hash}
            \ {PublicKeyOf(distributedLedger[n], h) :
                ledger[h].type \in {"send", "receive"}}
            \ {PublicKeyOf(distributedLedger[n], h) :
                ledger[h].type = "change"}
        IN SumMultiset({BalanceAt(distributedLedger[n], TopBlock(distributedLedger[n], pk)) : pk \in open})
           <= GenesisBalance

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

Spec ==
    /\ TRUE
    /\ UNCHANGED <<lastHash, distributedLedger, received>>

====