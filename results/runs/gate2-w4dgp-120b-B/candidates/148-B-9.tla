---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS Hash, CalculateHash(_,_,_), PrivateKey, PublicKey,
          KeyPair, Node, GenesisBalance, Ownership

VARIABLES lastHash, distributedLedger, received
ASSUME /\ \A d, o, n : CalculateHash(d, o, n) \in BOOLEAN
       /\ KeyPair \in [PrivateKey -> PublicKey]
       /\ GenesisBalance \in Nat
       /\ Ownership \in [Node -> PrivateKey]

NoHash == CHOOSE h \in Hash : TRUE
NoBlock == CHOOSE b \in [type: {"genesis","open","send","receive","change"},
                         account: PublicKey, balance: 0..GenesisBalance,
                         previous: Hash, source: Hash, rep: PublicKey,
                         destination: PublicKey] : TRUE
Ledger == [Hash -> [block: {NoBlock} \cup [type: {"genesis","open","send",
                                                 "receive","change"},
                                          account: PublicKey,
                                          balance: 0..GenesisBalance,
                                          previous: Hash,
                                          source: Hash,
                                          rep: PublicKey,
                                          destination: PublicKey],
                  signature: {NoBlock} \cup [data: Hash, signedWith: PrivateKey]]]

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET [block: {NoBlock} \cup [type: {"genesis",
                         "open","send","receive","change"}, account: PublicKey,
                         balance: 0..GenesisBalance, previous: Hash,
                         source: Hash, rep: PublicKey, destination: PublicKey],
                         signature: {NoBlock} \cup [data: Hash,
                         signedWith: PrivateKey]]]
    /\ \A n \in Node : Cardinality(received[n]) <= 1

\* Block hash chain lowers the coin balance at each send, so the running
\* total of all accounts can never exceed the genesis balance.
BalanceInvariant ==
    \A n \in Node :
        LET balances ==
            { h \in Hash : LET b = distributedLedger[n][h] IN b # NoBlock /\ b.block.type = "send"
                             : b.block.balance } IN
        Sum(balances) <= GenesisBalance

Spec == TRUE
====