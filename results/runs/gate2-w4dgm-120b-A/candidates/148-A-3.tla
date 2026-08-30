---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* The last block hash created; a hash is only ever created relative to a
\* known previous hash, so the set of reachable hashes is a function of the
\* action order that has already happened -- this is where the state space
\* explodes, and it is not truncated by any bounding scheme here.
VARIABLES lastHash, ledger, received

Account(y) == CHOOSE k \in PrivateKey : PublicKey[k] = y

RECURSIVE BalanceOf(_)
BalanceOf(g) == IF g = NoHash THEN 0
                ELSE IF g # NoHash /\ ledger[g] = NoBlockVal THEN 0
                ELSE IF g # NoHash /\ ledger[g].type = "send" THEN
                    BalanceOf(ledger[g].prev) - ledger[g].value
                ELSE IF g # NoHash /\ ledger[g].type = "receive" THEN
                    BalanceOf(ledger[g].prev) + ledger[g].value
                ELSE BalanceOf(ledger[g].prev)

RECURSIVE SumBalances(_)
SumBalances(S) == IF S = {} THEN 0
                  ELSE LET x == CHOOSE y \in S : TRUE IN BalanceOf(x) + SumBalances(S \ {x})

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger \in [Hash -> [type : {"send", "receive", "open", "change"}, prev : Hash \cup {NoHash}, src : PublicKey \cup {NoHash}, dst : PublicKey \cup {NoHash}, value : 0..GenesisBalance, signer : PrivateKey \cup {NoHash}, sig : 0..1]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node : \A g \in Hash :
        (ledger[g] # NoBlockVal /\ ledger[g].signer # NoHash) =>
            PublicKey[ledger[g].signer] = ledger[g].dst

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [g \in Hash |-> NoBlockVal]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock ==
    \E k \in PrivateKey :
        /\ \A g \in Hash : ledger[g] = NoBlockVal
        /\ \A n \in Node : Node' = Node /\ ledger' = [g \in Hash |-> [type |-> "open", prev |-> NoHash, src |-> NoHash, dst |-> PublicKey[k], value |-> GenesisBalance, signer |-> k, sig |-> 1]]
        /\ lastHash' = NoHashVal
        /\ UNCHANGED received

CreateSendBlock ==
    \E n \in Node, k \in PrivateKey, g \in Hash, v \in 1..GenesisBalance, d \in PublicKey :
        /\ ledger[g] = NoBlockVal
        /\ BalanceOf(g) >= v
        /\ ledger' = [ledger EXCEPT ![g] = [type |-> "send", prev |-> lastHash, src |-> PublicKey[k], dst |-> d, value |-> v, signer |-> k, sig |-> 1]]
        /\ lastHash' = g
        /\ received' = [m \in Node |-> received[m] \cup {g}]
        /\ UNCHANGED <<Node>>

CreateOpenBlock ==
    \E n \in Node, g \in Hash :
        /\ ledger[g] = NoBlockVal
        /\ ledger[g].type = "send"
        /\ ledger[g].dst = Account(Node[n])
        /\ ledger' = [ledger EXCEPT ![g] = [type |-> "open", prev |-> NoHash, src |-> NoHash, dst |-> ledger[g].dst, value |-> 0, signer |-> ledger[g].signer, sig |-> 1]]
        /\ lastHash' = g
        /\ received' = [m \in Node |-> received[m] \cup {g}]
        /\ UNCHANGED <<Node>>

CreateReceiveBlock ==
    \E n \in Node, g \in Hash, p \in Hash :
        /\ ledger[g] = NoBlockVal
        /\ ledger[p] # NoBlockVal
        /\ ledger[p].type = "send"
        /\ ledger[p].dst = Account(Node[n])
        /\ \A h \in Hash : ~(ledger[h] # NoBlockVal /\ ledger[h].type = "receive" /\ ledger[h].prev = p)
        /\ ledger' = [ledger EXCEPT ![g] = [type |-> "receive", prev |-> lastHash, src |-> NoHash, dst |-> Account(Node[n]), value |-> ledger[p].value, signer |-> ledger[p].signer, sig |-> 1]]
        /\ lastHash' = g
        /\ received' = [m \in Node |-> received[m] \cup {g}]
        /\ UNCHANGED <<Node>>

CreateChangeBlock ==
    \E n \in Node, g \in Hash, k \in PrivateKey :
        /\ ledger[g] = NoBlockVal
        /\ Account(Node[n]) = PublicKey[k]
        /\ ledger' = [ledger EXCEPT ![g] = [type |-> "change", prev |-> lastHash, src |-> NoHash, dst |-> PublicKey[k], value |-> 0, signer |-> k, sig |-> 1]]
        /\ lastHash' = g
        /\ received' = [m \in Node |-> received[m] \cup {g}]
        /\ UNCHANGED <<Node>>

ProcessBlock ==
    \E n \in Node, g \in received[n] :
        /\ ledger[g] # NoBlockVal
        /\ ledger' = [ledger EXCEPT ![g] = ledger[g]]
        /\ received' = [received EXCEPT ![n] = received[n] \ {g}]
        /\ UNCHANGED <<lastHash, Node>>

Next ==
    \/ CreateGenesisBlock
    \/ CreateSendBlock
    \/ CreateOpenBlock
    \/ CreateReceiveBlock
    \/ CreateChangeBlock
    \/ ProcessBlock

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

====