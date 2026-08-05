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
    /\ \A data, oldHash, newHash : CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

\* Signing a hash with a private key (hash, privateKey) and validation of
\* a signed hash against the expected public key and hash.
SignHash(hash, privateKey) ==
    [data |-> hash, signedWith |-> privateKey]

ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[signature.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ signature.data = expectedHash

Signature == [data : Hash, signedWith : PrivateKey]

Block ==
    [type : {"genesis"},
     account : PublicKey,
     balance : {GenesisBalance}]
    \cup [type : {"send"},
         previous : Hash,
         balance : 0 .. GenesisBalance,
         destination : PublicKey]
    \cup [type : {"open"},
         account : PublicKey,
         source : Hash,
         rep : PublicKey]
    \cup [type : {"receive"},
         previous : Hash,
         source : Hash]
    \cup [type : {"change"},
         previous : Hash,
         rep : PublicKey]

SignedBlock == [block : Block, signature : Signature]

NoBlock == CHOOSE b \in SignedBlock : FALSE
NoHash == CHOOSE h \in Hash : FALSE

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

\* Ledger property shortcuts.
GenesisBlockExists == lastHash /= NoHash

PublicKeyOf(ledger, hash) ==
    LET s == ledger[hash] IN
    IF s.block.type \in {"genesis", "open"}
    THEN s.block.account
    ELSE PublicKeyOf(ledger, s.block.previous)

IsAccountOpen(ledger, pk) ==
    \E h \in Hash : ledger[h] \notin {NoBlock} /\ ledger[h].block.account = pk

BalanceAt(ledger, hash) ==
    LET s == ledger[hash] IN
    CASE
        s.block.type = "open" -> BalanceAt(ledger, s.block.source)
      [] s.block.type = "send" -> s.block.balance
      [] s.block.type = "receive" ->
            BalanceAt(ledger, s.block.previous)
                + BalanceAt(ledger, s.block.source)
      [] s.block.type = "change" -> BalanceAt(ledger, s.block.previous)
      [] s.block.type = "genesis" -> s.block.balance

\* Signature checking on every ledger entry.
CryptographicInvariant ==
    \A n \in Node : \A h \in Hash :
        ledger[h] /= NoBlock =>
            ValidateSignature(ledger[h].signature,
                PublicKeyOf(ledger, h), h)

BalanceInvariant ==
    \A n \in Node :
        LET ledger == distributedLedger[n] IN
        LET openAccounts == { pk \in PublicKey : IsAccountOpen(ledger, pk) } IN
        LET topHashes == { CHOOSE h \in Hash :
                                ledger[h] \notin {NoBlock} /\
                                PublicKeyOf(ledger, h) = pk
                            : pk \in openAccounts } IN
        LET vbal(h) == BalanceAt(ledger, h) IN
        LET openBalances == BagOfAll(vbal, SetToBag(topHashes)) IN
        (GenesisBlockExists => (SumBag(openBalances) =< GenesisBalance))

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

Spec == TypeOK /\ CryptographicInvariant /\ BalanceInvariant

====