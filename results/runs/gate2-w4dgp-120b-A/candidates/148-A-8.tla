---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoHash, NoBlock

VARIABLES lastHash, ledger, received

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger \in [Node -> [Hash -> {NoBlockVal} \cup [key : PublicKey,
           prevKey : Hash \cup {NoHash}, kind : {"genesis", "send", "open", "receive", "change"},
           amount : 0..GenesisBalance]])
    /\ received \subseteq [Node -> {NoBlockVal} \cup [key : PublicKey,
           prevKey : Hash \cup {NoHash}, kind : {"genesis", "send", "open", "receive", "change"},
           amount : 0..GenesisBalance]]
    /\ NoHash \notin Hash
    /\ NoBlock \notin {NoBlockVal} \cup [key : PublicKey,
           prevKey : Hash \cup {NoHash}, kind : {"genesis", "send", "open", "receive", "change"},
           amount : 0..GenesisBalance]]

SignedBlock(key, prevKey, kind, amount) ==
    [key |-> key, prevKey |-> prevKey, kind |-> kind, amount |-> amount,
     sig |-> "SignedBy:" \o key]

RECURSIVE BalanceOf(_)
BalanceOf(S) ==
    IF S = {} THEN 0
    ELSE LET b == CHOOSE e \in S : TRUE IN b.amount + BalanceOf(S \ {b})

\* The account-chain balance is the sum of the block amounts belonging to blocks
\* whose genesis-root key equals the account's key.
RECURSIVE AccountBalance(_)
AccountBalance(S) ==
    IF S = {} THEN 0
    ELSE LET b == CHOOSE e \in S : TRUE IN
        LET rest == AccountBalance(S \ {b}) IN
        IF b.prevKey = NoHash THEN rest + b.amount
        ELSE rest

CoinsAreConserved == BalanceOf(ran ledger[CHOOSE n \in Node : TRUE]) <= GenesisBalance

\* The block-hash is a single value that advances every time a block is created;
\* it is used to order block creation, not to locate blocks.
BlockKey == CHOOSE h \in Hash : h \notin {lastHash} \cup {ledger[n][h].prevKey : n \in Node}
SignaturesAreValid ==
    \A n \in Node :
        \A h \in Hash :
            ledger[n][h] # NoBlockVal =>
                LET b == ledger[n][h] IN
                /\ b.sig = "SignedBy:" \o b.key
                /\ \A m \in Node :
                    IF m = n THEN TRUE
                    ELSE ledger[m][h] = NoBlockVal \/ ledger[m][h] = b

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {NoBlockVal}]

\* Every node must record the genesis block at the same hash so the network has
\* a common starting point.
CreateGenesisBlock(k) ==
    /\ lastHash = NoHashVal
    /\ k \in PrivateKey
    /\ lastHash' = BlockKey
    /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![BlockKey] = SignedBlock(k, NoHash, "genesis", GenesisBalance)]]
    /\ received' = [n \in Node |-> {}]

CreateSendBlock(n, k, amt) ==
    /\ lastHash # NoHashVal
    /\ k \in PrivateKey
    /\ amt <= AccountBalance(ran ledger[n])
    /\ lastHash' = BlockKey
    /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![BlockKey] = SignedBlock(k, lastHash, "send", amt)]]
    /\ received' = [m \in Node |-> received[m] \cup {SignedBlock(k, lastHash, "send", amt)}]

CreateOpenBlock(n, k) ==
    /\ lastHash # NoHashVal
    /\ k \in PrivateKey
    /\ lastHash' = BlockKey
    /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![BlockKey] = SignedBlock(k, lastHash, "open", 0)]]
    /\ received' = [m \in Node |-> received[m] \cup {SignedBlock(k, lastHash, "open", 0)}]

CreateReceiveBlock(n, k) ==
    /\ lastHash # NoHashVal
    /\ k \in PrivateKey
    /\ lastHash' = BlockKey
    /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![BlockKey] = SignedBlock(k, lastHash, "receive", 0)]]
    /\ received' = [m \in Node |-> received[m] \cup {SignedBlock(k, lastHash, "receive", 0)}]

CreateChangeBlock(n, k) ==
    /\ lastHash # NoHashVal
    /\ k \in PrivateKey
    /\ lastHash' = BlockKey
    /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![BlockKey] = SignedBlock(k, lastHash, "change", 0)]]
    /\ received' = [m \in Node |-> received[m] \cup {SignedBlock(k, lastHash, "change", 0)}]

ProcessReceivedBlock(n) ==
    /\ \E b \in received[n] :
        /\ \A m \in Node : ledger[m][b.prevKey] # NoBlockVal => ledger[m][b.prevKey].key = b.key
        /\ \A m \in Node : ledger[m][b.prevKey] \in {NoBlockVal, SignedBlock(b.key, b.prevKey, b.kind, b.amount)}
        /\ \A m \in Node : ledger[m][b.prevKey].kind = "send" => b.kind \in {"open", "receive"}
        /\ b.kind = "send" => b.amount <= AccountBalance(ran ledger[n])
        /\ \A m \in Node : ledger[m][b.prevKey].kind \in {"open", "receive", "change"} => b.kind # "send"
        /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![b.prevKey] = b]]
        /\ received' = [received EXCEPT ![n] = received[n] \ {b}]
    /\ UNCHANGED lastHash

Next ==
    \/ \E k \in PrivateKey : CreateGenesisBlock(k) \/ CreateSendBlock(CHOOSE n \in Node : TRUE, k, 1)
    \/ \E n \in Node, k \in PrivateKey :
           \/ CreateSendBlock(n, k, 1)
           \/ CreateOpenBlock(n, k)
           \/ CreateReceiveBlock(n, k)
           \/ CreateChangeBlock(n, k)
    \/ \E n \in Node : ProcessReceivedBlock(n)

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

====