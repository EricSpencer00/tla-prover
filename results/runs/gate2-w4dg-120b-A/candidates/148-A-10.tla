---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Recursive balance computation for an account's chain.
RECURSIVE SumChain(_)
SumChain(h) == IF h = NoHash THEN 0 ELSE LET b == ledger[NoHash][h] IN b.amount + SumChain(b.prevHash)

Balances == {SumChain(h) : h \in Hash}

RECURSIVE SumBalances(_)
SumBalances(S) == IF S = {} THEN 0
                  ELSE LET h == CHOOSE x \in S : TRUE IN SumChain(h) + SumBalances(S \ {h})

BalanceInvariant == SumBalances(Hash) <= GenesisBalance

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger \in [Node -> [Hash -> [kind : {"genesis", "send", "open", "receive", "change"}, prevHash : Hash \cup {NoHash}, src : PublicKey \cup {NoHash}, dst : PublicKey \cup {NoHash}, amount : Nat, owner : PublicKey, sig : PublicKey]]]
    /\ received \in [Node -> SUBSET Hash]

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\* Genesis block: the whole coin supply, added to every node at once.
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E k \in PrivateKey :
         /\ lastHash' = CalculateHash("genesis", NoHash, NoHash, NoHash, GenesisBalance)
         /\ \A n \in Node :
              ledger' = [ledger EXCEPT ![n][lastHash'] = [kind |-> "genesis", prevHash |-> NoHash, src |-> NoHash, dst |-> NoHash, amount |-> GenesisBalance, owner |-> PublicKey[k], sig |-> PublicKey[k]]]
    /\ UNCHANGED received

\* Send block: debit the sender, reference their previous block.
CreateSend ==
    /\ lastHash # NoHashVal
    /\ \E k \in PrivateKey, r \in PublicKey, a \in Nat :
         /\ SumChain(lastHash) >= a
         /\ lastHash' = CalculateHash("send", lastHash, PublicKey[k], r, a)
         /\ \A n \in Node :
              ledger' = [ledger EXCEPT ![n][lastHash'] = [kind |-> "send", prevHash |-> lastHash, src |-> PublicKey[k], dst |-> r, amount |-> a, owner |-> PublicKey[k], sig |-> PublicKey[k]]]
    /\ UNCHANGED received

\* Open block: the first block of an account that received funds.
CreateOpen ==
    /\ lastHash # NoHashVal
    /\ \E k \in PrivateKey, h \in Hash :
         /\ ledger[NoHash][h] # NoBlockVal
         /\ ledger[NoHash][h].kind = "send"
         /\ ledger[NoHash][h].dst = PublicKey[k]
         /\ ~(\E x \in Hash : ledger[NoHash][x] # NoBlockVal /\ ledger[NoHash][x].kind = "open" /\ ledger[NoHash][x].prevHash = h)
         /\ lastHash' = CalculateHash("open", h, NoHash, PublicKey[k], 0)
         /\ \A n \in Node :
              ledger' = [ledger EXCEPT ![n][lastHash'] = [kind |-> "open", prevHash |-> h, src |-> NoHash, dst |-> PublicKey[k], amount |-> 0, owner |-> PublicKey[k], sig |-> PublicKey[k]]]
    /\ UNCHANGED received

\* Receive block: credit the receiver, reference both the sender and receiver's chains.
CreateReceive ==
    /\ lastHash # NoHashVal
    /\ \E k \in PrivateKey, h \in Hash :
         /\ ledger[NoHash][h] # NoBlockVal
         /\ ledger[NoHash][h].kind \in {"send", "open"}
         /\ ledger[NoHash][h].dst = PublicKey[k]
         /\ \E x \in Hash : ledger[NoHash][x] # NoBlockVal /\ ledger[NoHash][x].kind = "receive" /\ ledger[NoHash][x].prevHash = lastHash
         /\ lastHash' = CalculateHash("receive", lastHash, NoHash, PublicKey[k], ledger[NoHash][h].amount)
         /\ \A n \in Node :
              ledger' = [ledger EXCEPT ![n][lastHash'] = [kind |-> "receive", prevHash |-> lastHash, src |-> NoHash, dst |-> PublicKey[k], amount |-> ledger[NoHash][h].amount, owner |-> PublicKey[k], sig |-> PublicKey[k]]]
    /\ UNCHANGED received

\* Change representative block: a node changes its voting delegate.
CreateChange ==
    /\ lastHash # NoHashVal
    /\ \E k \in PrivateKey :
         /\ lastHash' = CalculateHash("change", lastHash, PublicKey[k], NoHash, 0)
         /\ \A n \in Node :
              ledger' = [ledger EXCEPT ![n][lastHash'] = [kind |-> "change", prevHash |-> lastHash, src |-> NoHash, dst |-> NoHash, amount |-> 0, owner |-> PublicKey[k], sig |-> PublicKey[k]]]
    /\ UNCHANGED received

\* Broadcast every created block to all nodes' received channels.
Broadcast ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node :
         /\ lastHash \notin received[n]
         /\ received' = [received EXCEPT ![n] = @ \cup {lastHash}]
    /\ UNCHANGED <<lastHash, ledger>>

\* Processing validates signatures, references, and block-specific rules.
Process ==
    /\ \E n \in Node :
         /\ \E h \in received[n] :
              /\ ledger[n][h] = NoBlockVal
              /\ ledger[NoHash][h].sig = ledger[NoHash][h].owner
              /\ (IF ledger[NoHash][h].prevHash # NoHash THEN ledger[n][ledger[NoHash][h].prevHash] # NoBlockVal ELSE TRUE)
              /\ ledger' = [ledger EXCEPT ![n][h] = ledger[NoHash][h]]
              /\ received' = [received EXCEPT ![n] = @ \ {h}]
    /\ UNCHANGED lastHash

Next == CreateGenesis \/ CreateSend \/ CreateOpen \/ CreateReceive \/ CreateChange \/ Broadcast \/ Process

Spec == Init /\ [][Next]_vars

SafetyInvariant ==
    /\ \A n \in Node, h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].sig = ledger[n][h].owner
    /\ BalanceInvariant

====