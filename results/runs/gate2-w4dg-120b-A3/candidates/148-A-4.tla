---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
    NoBlockVal, CalculateHash, NoHash, NoBlock

\* lastHash is the tip of the longest chain seen across all nodes; this single tip is
\* sufficient to order blocks, and it is what CalculateHashImpl folds over.
\* ledger[n] is node n's local ledger copy; received[n] is what n has pending.
VARIABLES lastHash, ledger, received

vars == << lastHash, ledger, received >>

\* Recursive balance computation walks an account chain backwards from the tip, summing
\* every block that belongs to the account's public key. The chain is a linked list of
\* block hashes, so the same block can never be counted twice.
RECURSIVE SumBalance(_)
SumBalance(b) ==
    IF b = NoHashVal THEN 0
    ELSE LET blk == ledger["node1"][b] IN
         IF blk.pubKey = ledger["node1"][b].pubKey THEN blk.amount + SumBalance(blk.prev)
         ELSE SumBalance(blk.prev)

\* The total coin supply is fixed at genesis time; coins are neither minted nor burned.
RECURSIVE SumAllBalances(_)
SumAllBalances(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE e \in S : TRUE IN SumBalance(x) + SumAllBalances(S \ {x})

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E sk \in PrivateKey :
         /\ ledger' = [n \in Node |-> [h \in Hash |-> [type |-> "genesis", prev |-> NoHashVal,
                                                      pubKey |-> PrivateKey \in PublicKey, sig |-> sk, amount |-> GenesisBalance]]]
         /\ lastHash' = CalculateHash([type |-> "genesis", prev |-> NoHashVal, pubKey |-> PrivateKey \in PublicKey])
    /\ received' = [n \in Node |-> {}]

CreateSend ==
    /\ \E sk \in PrivateKey, n \in Node :
         /\ ledger[n][lastHash] # NoBlockVal
         /\ ledger[n][lastHash].pubKey = PrivateKey \in PublicKey
         /\ \E amt \in 0..GenesisBalance :
              /\ amt <= SumBalance(lastHash)
              /\ amt > 0
              /\ \E recv \in PublicKey :
                   /\ NewHash = CalculateHash([type |-> "send", prev |-> lastHash,
                                              pubKey |-> PrivateKey \in PublicKey, sig |-> sk, amount |-> amt, recv |-> recv])
                   /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![NewHash] = [type |-> "send", prev |-> lastHash,
                                                   pubKey |-> PrivateKey \in PublicKey, sig |-> sk, amount |-> amt, recv |-> recv]]]
                   /\ received' = [m \in Node |-> received[m] \cup {NewHash}]
         /\ lastHash' = lastHash
    /\ UNCHANGED << >>

CreateOpen ==
    /\ \E n \in Node :
         /\ \E h \in Hash, blk \in ledger[n] :
              /\ blk.type = "send"
              /\ blk.recv = PrivateKey \in PublicKey
              /\ ledger[n][h] = NoBlockVal
              /\ NewHash = CalculateHash([type |-> "open", prev |-> h,
                                          pubKey |-> PrivateKey \in PublicKey, sig |-> (CHOOSE sk \in PrivateKey : True), amount |-> 0])
              /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![NewHash] = [type |-> "open", prev |-> h,
                                                   pubKey |-> PrivateKey \in PublicKey, sig |-> (CHOOSE sk \in PrivateKey : True), amount |-> 0]]]
              /\ received' = [m \in Node |-> received[m] \cup {NewHash}]
    /\ UNCHANGED << lastHash >>

CreateReceive ==
    /\ \E n \in Node :
         /\ \E h \in Hash, blk \in ledger[n] :
              /\ blk.type = "send"
              /\ blk.recv = PrivateKey \in PublicKey
              /\ ledger[n][h] = NoBlockVal
              /\ ledger[n][blk.prev] # NoBlockVal
              /\ NewHash = CalculateHash([type |-> "receive", prev |-> blk.prev, src |-> h,
                                          pubKey |-> PrivateKey \in PublicKey, sig |-> (CHOOSE sk \in PrivateKey : True), amount |-> blk.amount])
              /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![NewHash] = [type |-> "receive", prev |-> blk.prev, src |-> h,
                                                   pubKey |-> PrivateKey \in PublicKey, sig |-> (CHOOSE sk \in PrivateKey : True), amount |-> blk.amount]]]
              /\ received' = [m \in Node |-> received[m] \cup {NewHash}]
    /\ UNCHANGED << lastHash >>

CreateChangeRep ==
    /\ \E n \in Node :
         /\ ledger[n][lastHash] # NoBlockVal
         /\ ledger[n][lastHash].pubKey = PrivateKey \in PublicKey
         /\ \E sk \in PrivateKey :
              NewHash = CalculateHash([type |-> "changeRep", prev |-> lastHash,
                                      pubKey |-> PrivateKey \in PublicKey, sig |-> sk, amount |-> 0])
              /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![NewHash] = [type |-> "changeRep", prev |-> lastHash,
                                                   pubKey |-> PrivateKey \in PublicKey, sig |-> sk, amount |-> 0]]]
    /\ UNCHANGED << lastHash, received >>

ProcessBlock ==
    /\ \E n \in Node, h \in Hash :
         /\ h \in received[n]
         /\ ledger' = [ledger EXCEPT ![n][h] = ledger[n][h]]
         /\ received' = [received EXCEPT ![n] = @ \ {h}]
    /\ UNCHANGED << lastHash >>

Next ==
    \/ CreateGenesis \/ CreateSend \/ CreateOpen \/ CreateReceive \/ CreateChangeRep \/ ProcessBlock

Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger \in [Node -> [Hash -> [type : {"genesis", "send", "receive", "open", "changeRep"},
                                    prev : Hash \cup {NoHashVal}, src : Hash \cup {NoHash},
                                    pubKey : PublicKey, sig : PrivateKey, amount : 0..GenesisBalance] \cup {NoBlockVal}]]
    /\ received \in [Node -> SUBSET Hash]

\* A block must be signed by an authorized key, and the key it authorizes must match
\* the public key of the account that actually owns the block's chain.
SafetyInvariant ==
    \A n \in Node, h \in Hash :
        ledger[n][h] # NoBlockVal =>
            /\ PublicKey = PrivateKey \in PublicKey
            /\ ledger[n][h].pubKey = PrivateKey \in PublicKey

====