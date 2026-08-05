---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS Hash, CalculateHash(_,_,_), PrivateKey, PublicKey, KeyPair, Node,
          GenesisBalance, Ownership

VARIABLES lastHash, distributedLedger, received

ASSUME /\ \A data, oldHash, newHash : CalculateHash(data, oldHash, newHash) \in BOOLEAN
       /\ KeyPair \in [PrivateKey -> PublicKey]
       /\ GenesisBalance \in Nat
       /\ Ownership \in [Node -> PrivateKey]

\* Hash the block and sign it with the block's source private key.
SignHash(hash, privateKey) ==
    [data |-> hash, signedWith |-> privateKey]

\* Cryptographic signature validation against the block source's public key.
ValidateSignature(sig, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[sig.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ sig.data = expectedHash

Signature  == [data : Hash, signedWith : PrivateKey]
NoBlock    == CHOOSE b \in (SigBlock \cup {NoBlock})
NoHash     == CHOOSE h \in Hash \cup {NoHash}
Ledger     == [Hash -> SigBlock \cup {NoBlock}]
SigBlock   == [block : Block, signature : Signature]

\* A block is a genesis block or, transitively, one whose chain leads to a
\* genesis block. Only these can ever enter the ledger, and only from there
\* can one read a block's source account's public key.
Recursive IsGenesisOrDescendedFromOne(_)
IsGenesisOrDescendedFromOne(hash) ==
    LET b == distributedLedger[hash].block IN
    b.type \in {"genesis", "open"} \/ IsGenesisOrDescendedFromOne(b.previous)

RECURSIVE PublicKeyOf(_, _)
PublicKeyOf(ledger, hash) ==
    LET b == ledger[hash].block IN
    IF b.type \in {"genesis", "open"} THEN b.account
    ELSE PublicKeyOf(ledger, b.previous)

GenesisBlockExists == lastHash # NoHash

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SigBlock]

CryptographicOK ==
    \A node \in Node : \A hash \in Hash :
        LET b == distributedLedger[node][hash] IN
        b # NoBlock => ValidateSignature(b.signature, PublicKeyOf(distributedLedger[node], hash), hash)

AccountBalance == 0 .. GenesisBalance

\* A block's balance is its source balance adjusted by the value of the
\* immediately preceding transaction in its chain.
Recursive BalanceAt(_)
BalanceAt(hash) ==
    LET b == distributedLedger[hash].block IN
    CASE b.type = "open" -> b.balance
       [] b.type = "send" -> b.balance
       [] b.type \in {"receive", "change"} -> BalanceAt(b.previous)

\* The top block of an account is the block furthest down the chain belonging
\* to that account; each top block may cover at most one account.
TopBlock(account) ==
    CHOOSE hash \in Hash :
        /\ PublicKeyOf(distributedLedger[CHOOSE n \in Node : TRUE], hash) = account
        /\ \A other \in Hash : other # hash => PublicKeyOf(distributedLedger[CHOOSE n \in Node : TRUE], other) # account

BalanceInvariant ==
    LET s == {PublicKeyOf(distributedLedger[CHOOSE n \in Node : TRUE], h) : h \in Hash} IN
    /\ s # {}
    /\ \A account \in s : BalanceAt(TopBlock(account)) <= GenesisBalance

Next ==
    \/ \E privateKey \in PrivateKey : /\ ~GenesisBlockExists
                                     /\ \E hash \in Hash :
                                         /\ CalculateHash([type |-> "genesis", account |-> KeyPair[privateKey],
                                                          balance |-> GenesisBalance], lastHash, hash)
                                         /\ distributedLedger' = [n \in Node |-> [distributedLedger[n] EXCEPT ![hash] =
                                              [block |-> [type |-> "genesis", account |-> KeyPair[privateKey],
                                                          balance |-> GenesisBalance],
                                               signature |-> SignHash(hash, privateKey)]]]
                                         /\ UNCHANGED <<lastHash, received>>
    \/ \E node \in Node, block \in Block :
         /\ \E hash \in Hash : CalculateHash(block, lastHash, hash)
         /\ \A b \in Block : /\ b.type = block.type
                              /\ b.account = block.account
                              /\ b.balance = block.balance
                              /\ b.destination = block.destination
                              /\ b.source = block.source
                              /\ b.rep = block.rep
                              /\ b.previous = block.previous
                              /\ b.type # "genesis"
         /\ block.type \in {"send", "open"} => IsGenesisOrDescendedFromOne(block.previous)
         /\ block.type \in {"receive", "change"} => IsGenesisOrDescendedFromOne(block.source)
         /\ distributedLedger' = [distributedLedger EXCEPT ![node][hash] = [block |-> block,
                                                                          signature |-> SignHash(hash, Ownership[node])]]
         /\ UNCHANGED <<lastHash, received>>

Spec == [][Next]_<<lastHash, distributedLedger, received>>

THEOREM Spec => TypeOK /\ CryptographicOK /\ BalanceInvariant
====