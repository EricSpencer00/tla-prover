---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Hash,           \* The universe of valid block hashes
    NoHashVal,      \* Sentinel value meaning "no hash yet"
    PrivateKey,    \* Set of all private keys in the system
    PublicKey,     \* Set of all public keys in the system
    Node,          \* Set of all network nodes
    GenesisBalance,\* Total coin supply (natural number)
    NoBlockVal,    \* Sentinel representing "no block"
    CalculateHash, \* Abstract hash function: (data, prevHash) -> Hash
    NoHash,        \* Alias of NoHashVal (used in constants list)
    NoBlock        \* Alias of NoBlockVal (used in constants list)

(* ------------------------------------------------------------------------ *)
(* Types *)
HashType               == Hash \cup {NoHash}
BlockHash              == [type : {"send","receive","open","change","genesis"},
                           data : STRING,
                           prev : Hash,
                           sender : PublicKey,
                           receiver : PublicKey,
                           amount : Nat,
                           rep : PublicKey,
                           signature : STRING]   \* abstract representation
Block                  == BlockHash \cup {NoBlock}
Ledger                 == [h \in Hash |-> Block]   \* maps each hash to a block or NoBlock
ReceivedSet            == SUBSET Hash                \* set of blocks pending validation

(* ------------------------------------------------------------------------ *)
(* Variables *)
VARIABLES
    lastHash,   \* The most recent block hash known globally
    ledgers,    \* Mapping each node to its Ledger
    received    \* Mapping each node to its set of received-but-unvalidated hashes

(* ------------------------------------------------------------------------ *)
(* Helper definitions *)

(* The set of all key pairs *)
KeyPair == [pk \in PublicKey |-> CHOOSE priv \in PrivateKey :
                         PrivateToPublic[priv] = pk]

(* Abstract signature function: signs block data with a private key *)
Signature(priv, block) == "sig_" \o priv \o "_" \o block.type

(* Verify that a block's signature matches the owner of the chain *)
SignatureValid(block) ==
    IF block.type = "genesis" THEN
        \E priv \in PrivateKey :
            block.signature = Signature(priv, block) /\ 
            KeyPair[block.sender] = priv
    ELSE
        \E priv \in PrivateKey :
            block.signature = Signature(priv, block) /\
            KeyPair[block.sender] = priv

(* Balance computation for a given account on a given node's ledger *)
Balance(node, acc) ==
    LET
        chain == {h \in Hash :
                    ledgers[node][h] # NoBlock /\ 
                    ledgers[node][h].sender = acc}
        amounts == { IF ledgers[node][h].type = "receive" THEN
                        ledgers[node][h].amount
                    ELSE IF ledgers[node][h].type = "send" THEN
                        -ledgers[node][h].amount
                    ELSE 0
                    : h \in chain }
    IN  IF chain = {} THEN 0 ELSE (IF amounts = {} THEN 0 ELSE
        LET b == Sum(amounts) IN IF b < 0 THEN 0 ELSE b)

(* ------------------------------------------------------------------------ *)
(* Initial state *)

Init ==
    /\ lastHash = NoHash
    /\ ledgers = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

(* ------------------------------------------------------------------------ *)
(* Actions *)

(* Broadcast a new block to all nodes' received sets *)
Broadcast(node, h) ==
    /\ h \in Hash
    /\ \A n \in Node : received' = [received EXCEPT ![n] = @ \cup {h}]
    /\ UNCHANGED <<lastHash, ledgers>>

CreateGenesis(node) ==
    /\ lastHash = NoHash               \* can only happen at start
    /\ node \in Node
    /\ \A n \in Node : ledgers[n] = [h \in Hash |-> NoBlock]  \* all empty
    /\ LET blk == [type |-> "genesis",
                   data |-> "genesis block",
                   prev |-> NoHash,
                   sender |-> CHOOSE pk \in PublicKey : TRUE,
                   receiver |-> CHOOSE pk \in PublicKey : TRUE,
                   amount |-> GenesisBalance,
                   rep |-> CHOOSE pk \in PublicKey : TRUE,
                   signature |-> Signature(CHOOSE priv \in PrivateKey :
                                             KeyPair[blk.sender] = priv, blk)]
       IN /\ h == CalculateHash(blk, NoHash)
          /\ h \in Hash
          /\ lastHash' = h
          /\ ledgers' = [n \in Node |-> [ledgers[n] EXCEPT ![h] = blk]]
          /\ received' = [n \in Node |-> {}]
    /\ UNCHANGED <<>>

Send(node, to, amt) ==
    /\ node \in Node
    /\ to \in PublicKey
    /\ amt \in Nat
    /\ Balance(node, KeyPair[node]) >= amt
    /\ LET prevBlock == 
            CHOOSE h \in Hash :
                ledgers[node][h] # NoBlock /\ 
                ledgers[node][h].sender = KeyPair[node] /\ 
                ledgers[node][h].type # "send"
       IN prevBlock \in Hash
    /\ LET blk == [type |-> "send",
                   data |-> "send",
                   prev |-> prevBlock,
                   sender |-> KeyPair[node],
                   receiver |-> to,
                   amount |-> amt,
                   rep |-> CHOOSE pk \in PublicKey : TRUE,
                   signature |-> Signature(CHOOSE priv \in PrivateKey :
                                             KeyPair[blk.sender] = priv, blk)]
       IN /\ h == CalculateHash(blk, prevBlock)
          /\ h \in Hash
          /\ lastHash' = h
          /\ ledgers' = [n \in Node |-> ledgers[n]]
          /\ received' = [n \in Node |-> received[n] \cup {h}]
    /\ UNCHANGED <<>>

Open(node, sendHash) ==
    /\ node \in Node
    /\ sendHash \in Hash
    /\ ledgers[node][sendHash].type = "send"
    /\ ledgers[node][sendHash].receiver = KeyPair[node]
    /\ LET blk == [type |-> "open",
                   data |-> "open",
                   prev |-> NoHash,
                   sender |-> KeyPair[node],
                   receiver |-> KeyPair[node],
                   amount |-> ledgers[node][sendHash].amount,
                   rep |-> CHOOSE pk \in PublicKey : TRUE,
                   signature |-> Signature(CHOOSE priv \in PrivateKey :
                                             KeyPair[blk.sender] = priv, blk)]
       IN /\ h == CalculateHash(blk, NoHash)
          /\ h \in Hash
          /\ lastHash' = h
          /\ ledgers' = [n \in Node |-> ledgers[n]]
          /\ received' = [n \in Node |-> received[n] \cup {h}]
    /\ UNCHANGED <<>>

Receive(node, recvPrev, sendHash) ==
    /\ node \in Node
    /\ recvPrev \in Hash
    /\ sendHash \in Hash
    /\ ledgers[node][recvPrev].type \in {"receive","send","open","change","genesis"}
    /\ ledgers[node][sendHash].type = "send"
    /\ ledgers[node][sendHash].receiver = KeyPair[node]
    /\ LET blk == [type |-> "receive",
                   data |-> "receive",
                   prev |-> recvPrev,
                   sender |-> KeyPair[node],
                   receiver |-> KeyPair[node],
                   amount |-> ledgers[node][sendHash].amount,
                   rep |-> CHOOSE pk \in PublicKey : TRUE,
                   signature |-> Signature(CHOOSE priv \in PrivateKey :
                                             KeyPair[blk.sender] = priv, blk)]
       IN /\ h == CalculateHash(blk, recvPrev)
          /\ h \in Hash
          /\ lastHash' = h
          /\ ledgers' = [n \in Node |-> ledgers[n]]
          /\ received' = [n \in Node |-> received[n] \cup {h}]
    /\ UNCHANGED <<>>

ChangeRep(node, newRep) ==
    /\ node \in Node
    /\ newRep \in PublicKey
    /\ LET prevBlock ==
            CHOOSE h \in Hash :
                ledgers[node][h] # NoBlock /\ 
                ledgers[node][h].sender = KeyPair[node] /\ 
                ledgers[node][h].type # "change"
       IN prevBlock \in Hash
    /\ LET blk == [type |-> "change",
                   data |-> "change",
                   prev |-> prevBlock,
                   sender |-> KeyPair[node],
                   receiver |-> KeyPair[node],
                   amount |-> 0,
                   rep |-> newRep,
                   signature |-> Signature(CHOOSE priv \in PrivateKey :
                                             KeyPair[blk.sender] = priv, blk)]
       IN /\ h == CalculateHash(blk, prevBlock)
          /\ h \in Hash
          /\ lastHash' = h
          /\ ledgers' = [n \in Node |-> ledgers[n]]
          /\ received' = [n \in Node |-> received[n] \cup {h}]
    /\ UNCHANGED <<>>

(* Process a received block on a node *)
Process(node) ==
    /\ node \in Node
    /\ \E h \in received[node] :
        /\ blk == ledgers[node][h]
        /\ blk # NoBlock
        /\ SignatureValid(blk)
        /\ /\ IF blk.type = "send" THEN
                Balance(node, blk.sender) >= blk.amount
           ELSE TRUE
        /\ /\ IF blk.type = "receive" THEN
                \E sendH \in Hash :
                    ledgers[node][sendH].type = "send" /\
                    ledgers[node][sendH].receiver = blk.sender /\
                    ledgers[node][sendH].amount = blk.amount
           ELSE TRUE
        /\ /\ IF blk.type = "open" THEN
                \E sendH \in Hash :
                    ledgers[node][sendH].type = "send" /\
                    ledgers[node][sendH].receiver = blk.sender
           ELSE TRUE
        /\ /\ IF blk.type = "change" THEN TRUE
           ELSE TRUE
        /\ ledgers' = [n \in Node |-> 
                        IF n = node THEN [ledgers[n] EXCEPT ![h] = blk] ELSE ledgers[n]]
        /\ received' = [n \in Node |-> 
                        IF n = node THEN @ \ {h} ELSE received[n]]
    /\ UNCHANGED lastHash

(* Non-deterministic step: either create a block or process a received one *)
Next ==
    \/ \E n \in Node : CreateGenesis(n)
    \/ \E n \in Node, to \in PublicKey, a \in Nat : Send(n, to, a)
    \/ \E n \in Node, sh \in Hash : Open(n, sh)
    \/ \E n \in Node, rp \in Hash, sh \in Hash : Receive(n, rp, sh)
    \/ \E n \in Node, nr \in PublicKey : ChangeRep(n, nr)
    \/ \E n \in Node : Process(n)

(* ------------------------------------------------------------------------ *)
(* Specification *)
Spec == Init /\ [][Next]_<<lastHash, ledgers, received>>

(* ------------------------------------------------------------------------ *)
(* Invariants *)

TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledgers \in [Node -> [Hash -> Block]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            ledgers[n][h] # NoBlock => SignatureValid(ledgers[n][h])

(* ------------------------------------------------------------------------ *)
THEOREM Spec => []TypeInvariant
THEOREM Spec => []SafetyInvariant

====