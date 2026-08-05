---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS
    Hash, CalculateHash(_,_,_), PrivateKey, PublicKey, KeyPair,
    Node, GenesisBalance, Ownership

ASSUME
    /\ \A d, o, n : CalculateHash(d, o, n) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

VARIABLES lastHash, distributedLedger, received

vars == <<lastHash, distributedLedger, received>>

Signature == [data: Hash, signedWith: PrivateKey]

NoBlock == CHOOSE b \in [type: {"none"}] : TRUE

Ledger == [Hash -> [block: [type: {"none", "genesis", "open", "send",
    "receive", "change"}, account: PublicKey, balance: Nat,
    destination: PublicKey, previous: Hash, source: Hash, rep: PublicKey],
    signature: Signature] \cup {NoBlock}]

HashRange == 2

NoHash == CHOOSE h \in Hash : TRUE

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

SignHash(h, k) == [data |-> h, signedWith |-> k]

ValidateSignature(sig, pk, h) ==
    /\ KeyPair[sig.signedWith] = pk
    /\ sig.data = h

GenesisBlockExists ==
    /\ lastHash # NoHash

PublicKeyOf(hash, n) ==
    LET block == distributedLedger[n][hash] IN
    IF block.block.type \in {"genesis", "open"}
    THEN block.block.account
    ELSE PublicKeyOf(block.block.previous, n)

BalanceAt(hash, n) ==
    LET block == distributedLedger[n][hash] IN
    CASE block.block.type = "open" -> BalanceAt(block.block.source, n)
    [] block.block.type = "send" -> block.block.balance
    [] block.block.type = "receive" ->
        BalanceAt(block.block.previous, n)
        + BalanceAt(block.block.source, n)
    [] block.block.type = "change" -> BalanceAt(block.block.previous, n)
    [] block.block.type = "genesis" -> block.block.balance

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> [Hash -> [block: [type: {"none",
        "genesis", "open", "send", "receive", "change"}, account: PublicKey,
        balance: Nat, destination: PublicKey, previous: Hash, source: Hash,
        rep: PublicKey], signature: Signature] \cup {NoBlock}]]
    /\ received \in [Node -> SUBSET [block: [type: {"none", "genesis",
        "open", "send", "receive", "change"}, account: PublicKey, balance: Nat,
        destination: PublicKey, previous: Hash, source: Hash, rep: PublicKey],
        signature: Signature]]

LogicallySound ==
    /\ \A n \in Node :
        \A h \in Hash : distributedLedger[n][h] # NoBlock =>
            ValidateSignature(
                distributedLedger[n][h].signature,
                PublicKeyOf(h, n), h)
    /\ \A n \in Node : \A h \in Hash :
        (\A m \in Hash : distributedLedger[n][m] # NoBlock /\ m # h =>
            PublicKeyOf(m, n) # PublicKeyOf(h, n))
            \/ BalanceAt(h, n) <= GenesisBalance

CreateBlock ==
    /\ \E n \in Node, k \in PrivateKey :
        /\ ~GenesisBlockExists
        /\ lastHash' = n
        /\ distributedLedger' = [distributedLedger EXCEPT ![n] =
            [h \in Hash |-> [block |-> [type |-> "genesis", account |-> KeyPair[k],
            balance |-> GenesisBalance, destination |-> NoHash, previous |-> NoHash,
            source |-> NoHash, rep |-> NoHash],
            signature |-> SignHash(h, k)]]]
        /\ UNCHANGED received

CreateOpenBlock ==
    /\ \E n \in Node, hk \in Hash, pk \in PublicKey :
        /\ lastHash' = n
        /\ distributedLedger' = [distributedLedger EXCEPT ![n][hk] =
            [block |-> [type |-> "open", account |-> pk, balance |-> 0,
            destination |-> NoHash, previous |-> NoHash, source |-> NoHash,
            rep |-> NoHash], signature |-> SignHash(hk, Ownership[n])]]
        /\ UNCHANGED received

CreateSendBlock ==
    /\ \E n \in Node, hk \in Hash, pk \in PublicKey, a \in Nat :
        /\ lastHash' = n
        /\ distributedLedger' = [distributedLedger EXCEPT ![n][hk] =
            [block |-> [type |-> "send", account |-> pk, balance |-> a,
            destination |-> pk, previous |-> NoHash, source |-> NoHash,
            rep |-> NoHash], signature |-> SignHash(hk, Ownership[n])]]
        /\ UNCHANGED received

CreateReceiveBlock ==
    /\ \E n \in Node, hk \in Hash, h1 \in Hash, h2 \in Hash:
        /\ lastHash' = n
        /\ distributedLedger' = [distributedLedger EXCEPT ![n][hk] =
            [block |-> [type |-> "receive", account |-> NoHash, balance |-> 0,
            destination |-> NoHash, previous |-> h1, source |-> h2,
            rep |-> NoHash], signature |-> SignHash(hk, Ownership[n])]]
        /\ UNCHANGED received

CreateChangeBlock ==
    /\ \E n \in Node, hk \in Hash, pk \in PublicKey :
        /\ lastHash' = n
        /\ distributedLedger' = [distributedLedger EXCEPT ![n][hk] =
            [block |-> [type |-> "change", account |-> NoHash, balance |-> 0,
            destination |-> pk, previous |-> NoHash, source |-> NoHash,
            rep |-> pk], signature |-> SignHash(hk, Ownership[n])]]
        /\ UNCHANGED received

Next == CreateBlock \/ CreateOpenBlock \/ CreateSendBlock \/ CreateReceiveBlock
    \/ CreateChangeBlock

Spec == Init /\ [][Next]_vars

Safety == Spec => TypeOK /\ LogicallySound

====