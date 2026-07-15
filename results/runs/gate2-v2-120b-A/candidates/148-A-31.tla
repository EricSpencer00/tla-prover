---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(* ----------------------------------------------------------------------
   Constants (to be instantiated in the .cfg)
   ---------------------------------------------------------------------- *)
CONSTANTS
    Hash,            \* Set of possible hash values
    NoHashVal,       \* sentinel value indicating the absence of a hash
    PrivateKey,      \* Set of private keys
    PublicKey,       \* Set of public keys
    Node,            \* Set of network nodes
    GenesisBalance,  \* Total number of coins in the system
    NoBlockVal,      \* sentinel value indicating the absence of a block
    CalculateHash,   \* Abstract hash function
    NoHash,          \* Alias for NoHashVal (for readability)
    NoBlock          \* Alias for NoBlockVal

(* ----------------------------------------------------------------------
   Derived sets
   ---------------------------------------------------------------------- *)
BLOCK_TYPE == {"Genesis", "Send", "Open", "Receive", "ChangeRep"}

(* ----------------------------------------------------------------------
   Types for readability
   ---------------------------------------------------------------------- *)
Account == PublicKey
Amount == Nat

(* ----------------------------------------------------------------------
   Block record definition
   ---------------------------------------------------------------------- *)
Block ==
    [type           : BLOCK_TYPE,
     hash           : Hash,
     prev           : Hash,
     account        : Account,
     amount         : Amount,
     target         : Account,
     source         : Hash,
     rep            : Account,
     signature      : [pk : PublicKey, sig : Nat]]

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES
    lastHash,      \* The most recent block hash known globally
    ledger,        \* [node \in Node -> [h \in Hash -> Block \cup {NoBlock}]]
    received,      \* [node \in Node -> SUBSET Hash]
    privKeyOf      \* [node \in Node -> PrivateKey]  (ownership mapping)

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

HashOf(b) == b.hash

(* Signature verification is abstract: a block is valid iff the signature
   field contains the public key that owns the account and a non‑zero value. *)
ValidSignature(b) ==
    /\ b.signature.pk = b.account
    /\ b.signature.sig # 0

(* Balance calculation walks the chain of a given account up to a given hash *)
Balance(acc, h) ==
    IF h = NoHashVal THEN 0
    ELSE
        LET b == ledger[Node][h] IN
        IF b = NoBlock THEN 0
        ELSE
            CASE b.type = "Genesis"   -> b.amount
               [] b.type = "Send"      -> Balance(acc, b.prev) - b.amount
               [] b.type = "Receive"   -> Balance(acc, b.prev) + b.amount
               [] b.type = "Open"      -> b.amount
               [] b.type = "ChangeRep" -> Balance(acc, b.prev)
               [] OTHER                -> Balance(acc, b.prev)

(* ----------------------------------------------------------------------
   Initial predicate
   ---------------------------------------------------------------------- *)
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]
    /\ privKeyOf = [n \in Node |-> CHOOSE k \in PrivateKey : TRUE]  \* arbitrary ownership

(* ----------------------------------------------------------------------
   Action definitions
   ---------------------------------------------------------------------- *)

(* Create Genesis block – may happen only when no block exists yet *)
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E n \in Node :
        LET pk == CHOOSE p \in PublicKey : TRUE IN
        LET b == [type       |-> "Genesis",
                  hash       |-> CHOOSE h \in Hash : TRUE,
                  prev       |-> NoHashVal,
                  account    |-> pk,
                  amount     |-> GenesisBalance,
                  target     |-> NoHashVal,
                  source     |-> NoHashVal,
                  rep        |-> NoHashVal,
                  signature  |-> [pk |-> pk, sig |-> 1]] IN
        /\ ValidSignature(b)
        /\ lastHash' = b.hash
        /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = b.hash THEN b ELSE ledger[n][h]]]
        /\ received' = [n \in Node |-> {}]
        /\ UNCHANGED <<privKeyOf>>

(* Helper: broadcast a new block hash to all nodes' received sets *)
Broadcast(h) ==
    [n \in Node |-> received[n] \cup {h}]

CreateSend(node, targetAcc, amt) ==
    /\ node \in Node
    /\ targetAcc \in Account
    /\ amt \in Nat
    /\ amt > 0
    /\ ledger[node][lastHash] # NoBlock
    /\ ledger[node][lastHash].account = privKeyOf[node] \* account ownership
    /\ Balance(ledger[node][lastHash].account, lastHash) >= amt
    /\ LET b == [type       |-> "Send",
                 hash       |-> CalculateHash([type |-> "Send",
                                                prev |-> lastHash,
                                                account |-> ledger[node][lastHash].account,
                                                amount |-> amt,
                                                target |-> targetAcc]),
                 prev       |-> lastHash,
                 account    |-> ledger[node][lastHash].account,
                 amount     |-> amt,
                 target     |-> targetAcc,
                 source     |-> NoHashVal,
                 rep        |-> NoHashVal,
                 signature  |-> [pk |-> ledger[node][lastHash].account,
                                sig |-> 1]]] IN
    /\ ValidSignature(b)
    /\ lastHash' = b.hash
    /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = b.hash THEN b ELSE ledger[n][h]]]
    /\ received' = Broadcast(b.hash)
    /\ UNCHANGED <<privKeyOf>>

CreateOpen(node, srcHash) ==
    /\ node \in Node
    /\ srcHash \in Hash
    /\ ledger[node][srcHash] # NoBlock
    /\ ledger[node][srcHash].type = "Send"
    /\ ledger[node][srcHash].target = privKeyOf[node] \* the account to be opened
    /\ LET b == [type       |-> "Open",
                 hash       |-> CalculateHash([type |-> "Open",
                                                prev |-> NoHashVal,
                                                account |-> ledger[node][srcHash].target,
                                                source |-> srcHash]),
                 prev       |-> NoHashVal,
                 account    |-> ledger[node][srcHash].target,
                 amount     |-> ledger[node][srcHash].amount,
                 target     |-> NoHashVal,
                 source     |-> srcHash,
                 rep        |-> NoHashVal,
                 signature  |-> [pk |-> ledger[node][srcHash].target,
                                sig |-> 1]]] IN
    /\ ValidSignature(b)
    /\ lastHash' = b.hash
    /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = b.hash THEN b ELSE ledger[n][h]]]
    /\ received' = Broadcast(b.hash)
    /\ UNCHANGED <<privKeyOf>>

CreateReceive(node, srcHash) ==
    /\ node \in Node
    /\ srcHash \in Hash
    /\ ledger[node][srcHash] # NoBlock
    /\ ledger[node][srcHash].type = "Send"
    /\ ledger[node][srcHash].target = privKeyOf[node]
    /\ ledger[node][lastHash] # NoBlock
    /\ ledger[node][lastHash].account = privKeyOf[node]
    /\ LET b == [type       |-> "Receive",
                 hash       |-> CalculateHash([type |-> "Receive",
                                                prev |-> lastHash,
                                                account |-> privKeyOf[node],
                                                source |-> srcHash]),
                 prev       |-> lastHash,
                 account    |-> privKeyOf[node],
                 amount     |-> ledger[node][srcHash].amount,
                 target     |-> NoHashVal,
                 source     |-> srcHash,
                 rep        |-> NoHashVal,
                 signature  |-> [pk |-> privKeyOf[node],
                                sig |-> 1]]] IN
    /\ ValidSignature(b)
    /\ lastHash' = b.hash
    /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = b.hash THEN b ELSE ledger[n][h]]]
    /\ received' = Broadcast(b.hash)
    /\ UNCHANGED <<privKeyOf>>

CreateChangeRep(node, newRep) ==
    /\ node \in Node
    /\ newRep \in Account
    /\ ledger[node][lastHash] # NoBlock
    /\ ledger[node][lastHash].account = privKeyOf[node]
    /\ LET b == [type       |-> "ChangeRep",
                 hash       |-> CalculateHash([type |-> "ChangeRep",
                                                prev |-> lastHash,
                                                account |-> privKeyOf[node],
                                                rep |-> newRep]),
                 prev       |-> lastHash,
                 account    |-> privKeyOf[node],
                 amount     |-> 0,
                 target     |-> NoHashVal,
                 source     |-> NoHashVal,
                 rep        |-> newRep,
                 signature  |-> [pk |-> privKeyOf[node],
                                sig |-> 1]]] IN
    /\ ValidSignature(b)
    /\ lastHash' = b.hash
    /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = b.hash THEN b ELSE ledger[n][h]]]
    /\ received' = Broadcast(b.hash)
    /\ UNCHANGED <<privKeyOf>>

(* Processing a received block: an arbitrary node picks a hash from its
   received set, validates it, and incorporates it into its ledger. *)
Process(node) ==
    /\ node \in Node
    /\ \E h \in received[node] :
        LET b == ledger[node][h] IN
        /\ b # NoBlock
        /\ ValidSignature(b)
        /\ /\ IF b.prev # NoHashVal THEN ledger[node][b.prev] # NoBlock ELSE TRUE
           /\ IF b.type = "Send" THEN
                 Balance(b.account, b.prev) >= b.amount
              ELSE TRUE
        /\ ledger' = [n \in Node |-> 
              IF n = node THEN
                 [h2 \in Hash |-> IF h2 = h THEN b ELSE ledger[n][h2]]
              ELSE ledger[n]]
        /\ received' = [n \in Node |-> 
              IF n = node THEN received[n] \ {h} ELSE received[n]]
        /\ UNCHANGED <<lastHash, privKeyOf>>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ CreateGenesis
    \/ \E node \in Node, target \in Account, amt \in Nat :
          CreateSend(node, target, amt)
    \/ \E node \in Node, src \in Hash :
          CreateOpen(node, src)
    \/ \E node \in Node, src \in Hash :
          CreateReceive(node, src)
    \/ \E node \in Node, newRep \in Account :
          CreateChangeRep(node, newRep)
    \/ \E node \in Node : Process(node)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<lastHash, ledger, received, privKeyOf>>

(* ----------------------------------------------------------------------
   Type invariant (ensures variables stay within their declared domains)
   ---------------------------------------------------------------------- *)
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]
    /\ privKeyOf \in [Node -> PrivateKey]
    /\ \A n \in Node :
        \A h \in Hash :
            ledger[n][h] = NoBlock \/ 
                /\ ledger[n][h].hash = h
                /\ ledger[n][h].type \in BLOCK_TYPE
                /\ ledger[n][h].account \in Account
                /\ ledger[n][h].signature.pk = ledger[n][h].account
                /\ ledger[n][h].signature.sig # 0

(* ----------------------------------------------------------------------
   Safety invariant (cryptographic invariant)
   ---------------------------------------------------------------------- *)
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            ledger[n][h] # NoBlock => ValidSignature(ledger[n][h])

====