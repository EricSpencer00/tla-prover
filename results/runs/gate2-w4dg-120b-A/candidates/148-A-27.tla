---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
    CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

KeyOf(account) == CHOOSE k \in PrivateKey : PUBLIC(key) = account

ChainAt(n, h) ==
    LET f[x \in Hash \cup {NoHash}] ==
        IF x = NoHash
        THEN NoBlock
        ELSE
            IF ledger[n][x] = NoBlockVal
            THEN NoBlock
            ELSE [hash |-> x, blk |-> ledger[n][x]]
    IN f[h]

BalanceOf(n, h) ==
    LET f[x \in Hash \cup {NoHash}] ==
        IF x = NoHash
        THEN 0
        ELSE
            IF ledger[n][x] = NoBlockVal
            THEN 0
            ELSE LET p == ledger[n][x].prev
                 IN IF ledger[n][x].type = "send"
                    THEN f[p] - ledger[n][x].amount
                    ELSE IF ledger[n][x].type = "receive"
                         THEN f[p] + ledger[n][x].amount
                         ELSE f[p]
    IN f[h]

SumBalances ==
    LET g[S \in SUBSET Node] ==
        IF S = {}
        THEN 0
        ELSE LET n == CHOOSE e \in S : TRUE
             IN BalanceOf(n, lastHash) + g[S \ {n}]
    IN g[Node]

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> {NoBlockVal} \cup [type: {"genesis", "send", "open", "receive", "changeRep"},
                                                     author: PublicKey, prev: Hash \cup {NoHash},
                                                     recipient: PublicKey, amount: 1..GenesisBalance, signature: 1..2]]]
    /\ received \in [Node -> SUBSET Hash]

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(k) ==
    /\ lastHash = NoHash
    /\ ledger' = [n \in Node |->
                    [h \in Hash |-> IF h = CalculateHash([type |-> "genesis", author |-> PUBLIC(k), prev |-> NoHash, amount |-> GenesisBalance])
                                  THEN [type |-> "genesis", author |-> PUBLIC(k), prev |-> NoHash,
                                        recipient |-> PUBLIC(k), amount |-> GenesisBalance, signature |-> 1]
                                  ELSE ledger[n][h]]]
    /\ lastHash' = CalculateHash([type |-> "genesis", author |-> PUBLIC(k), prev |-> NoHash, amount |-> GenesisBalance])
    /\ received' = [n \in Node |-> received[n] \cup {CalculateHash([type |-> "genesis", author |-> PUBLIC(k), prev |-> NoHash, amount |-> GenesisBalance])}]

CreateSendBlock(n, k, amt) ==
    /\ BalanceOf(n, lastHash) >= amt
    /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = CalculateHash([type |-> "send", author |-> PUBLIC(k), prev |-> lastHash, amount |-> amt])
                                   THEN [type |-> "send", author |-> PUBLIC(k), prev |-> lastHash, recipient |-> PUBLIC(k),
                                         amount |-> amt, signature |-> 1]
                                   ELSE ledger[n][h]]]
    /\ lastHash' = CalculateHash([type |-> "send", author |-> PUBLIC(k), prev |-> lastHash, amount |-> amt])
    /\ received' = [n' \in Node |-> received[n'] \cup {CalculateHash([type |-> "send", author |-> PUBLIC(k), prev |-> lastHash, amount |-> amt])}]

CreateOpenBlock(n, k, sendHash) ==
    /\ ChainAt(n, sendHash).type = "send"
    /\ ChainAt(n, sendHash).recipient = PUBLIC(k)
    /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = CalculateHash([type |-> "open", author |-> PUBLIC(k), prev |-> sendHash, amount |-> ChainAt(n, sendHash).amount])
                                   THEN [type |-> "open", author |-> PUBLIC(k), prev |-> sendHash,
                                         recipient |-> PUBLIC(k), amount |-> ChainAt(n, sendHash).amount,
                                         signature |-> 1]
                                   ELSE ledger[n][h]]]
    /\ lastHash' = CalculateHash([type |-> "open", author |-> PUBLIC(k), prev |-> sendHash, amount |-> ChainAt(n, sendHash).amount])
    /\ received' = [n' \in Node |-> received[n'] \cup {CalculateHash([type |-> "open", author |-> PUBLIC(k), prev |-> sendHash, amount |-> ChainAt(n, sendHash).amount])}]

CreateReceiveBlock(n, k, sendHash) ==
    /\ ChainAt(n, sendHash).type = "send"
    /\ ChainAt(n, sendHash).recipient = PUBLIC(k)
    /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = CalculateHash([type |-> "receive", author |-> PUBLIC(k), prev |-> lastHash,
                                                                    ref |-> sendHash, amount |-> ChainAt(n, sendHash).amount])
                                      THEN [type |-> "receive", author |-> PUBLIC(k), prev |-> lastHash,
                                            recipient |-> PUBLIC(k), amount |-> ChainAt(n, sendHash).amount,
                                            signature |-> 1]
                                      ELSE ledger[n][h]]]
    /\ lastHash' = CalculateHash([type |-> "receive", author |-> PUBLIC(k), prev |-> lastHash,
                                 ref |-> sendHash, amount |-> ChainAt(n, sendHash).amount])
    /\ received' = [n' \in Node |-> received[n'] \cup {CalculateHash([type |-> "receive", author |-> PUBLIC(k), prev |-> lastHash,
                                                                     ref |-> sendHash, amount |-> ChainAt(n, sendHash).amount])}]

CreateChangeRepBlock(n, k) ==
    /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = CalculateHash([type |-> "changeRep", author |-> PUBLIC(k), prev |-> lastHash])
                                   THEN [type |-> "changeRep", author |-> PUBLIC(k), prev |-> lastHash,
                                         recipient |-> PUBLIC(k), amount |-> 0, signature |-> 1]
                                   ELSE ledger[n][h]]]
    /\ lastHash' = CalculateHash([type |-> "changeRep", author |-> PUBLIC(k), prev |-> lastHash])
    /\ received' = [n' \in Node |-> received[n'] \cup {CalculateHash([type |-> "changeRep", author |-> PUBLIC(k), prev |-> lastHash])}]

ValidateReceiveBlock(n, h) ==
    /\ h \in received[n]
    /\ ledger[n][h] # NoBlockVal
    /\ LET blk == ledger[n][h] IN
         /\ ChainAt(n, blk.prev) # NoBlock
         /\ blk.signature \in 1..2
         /\ blk.type = "receive" => ChainAt(n, blk.ref) # NoBlock
    /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
    /\ UNCHANGED <<lastHash, ledger>>

Next ==
    \/ \E k \in PrivateKey : CreateGenesisBlock(k)
    \/ \E n \in Node, k \in PrivateKey, amt \in 1..GenesisBalance : CreateSendBlock(n, k, amt)
    \/ \E n \in Node, k \in PrivateKey, h \in Hash : CreateOpenBlock(n, k, h) \/ CreateReceiveBlock(n, k, h)
    \/ \E n \in Node, k \in PrivateKey : CreateChangeRepBlock(n, k)
    \/ \E n \in Node, h \in Hash : ValidateReceiveBlock(n, h)

Spec == Init /\ [][Next]_vars

SafetyInvariant ==
    \A n \in Node, h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].signature \in 1..2

====