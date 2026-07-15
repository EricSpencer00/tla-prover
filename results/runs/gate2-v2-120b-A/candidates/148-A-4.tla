---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Hash,          \* set of all possible block hashes
    NoHashVal,     \* sentinel value for “no hash yet”
    PrivateKey,    \* set of private keys
    PublicKey,     \* set of public keys
    Node,          \* set of network nodes
    GenesisBalance,\* total coin supply (a natural number)
    NoBlockVal,    \* sentinel value for “no block”
    CalculateHash, \* abstract hash function
    NoHash,        \* alias for NoHashVal (used in record fields)
    NoBlock        \* alias for NoBlockVal (used in record fields)

(* ────────────────────────────────────────────────────────────── *)
(* Types and basic data structures                               *)
(* ────────────────────────────────────────────────────────────── *)

ACCOUNT == PublicKey

(* A Block is a record that contains at least the fields we need.
   Other fields (e.g., amount, representative) are modeled as Naturals
   or strings for simplicity.                       *)
BlockRecord ==
    [ type          : {"genesis", "send", "open", "receive", "change"},
      prevHash      : Hash,
      srcHash       : Hash,       \* for receive/open blocks: referenced send block
      dst           : PUBLICKEY, \* destination account for send/open
      amount        : Nat,
      rep           : PUBLICKEY, \* representative (for change)
      signer        : PublicKey,
      signature     : Nat,        \* abstract signature (treated as Nat)
      hash          : Hash ]

NoBlock == NoBlockVal

VARIABLES
    lastHash,          \* the most recent block hash known globally
    ledgers,           \* [node -> [hash -> BlockRecord]]
    received           \* [node -> SUBSET Hash]

(* ────────────────────────────────────────────────────────────── *)
(* Helper definitions                                            *)
(* ────────────────────────────────────────────────────────────── *)

\* Types for readability
NodeSet == Node
HashSet == Hash

\* Initial (empty) ledger mapping
EmptyLedger == [ h \in Hash |-> NoBlock ]

\* Initial received set
EmptyReceived == {}

\* The set of all possible account chains (useful for balance computation)
AccountChains == { a \in PUBLICKEY : TRUE }

\* Abstract signature verification (always true if the signer matches the
   public key; real crypto is omitted) *)
SignatureValid(sig, pk) == TRUE

\* Abstract function to compute a block's hash – modeled by the constant
   CalculateHash. It is expected to be injective enough for the model. *)
BlockHash(b) == CalculateHash(b)

\* Balance of an account on a given node – walks the chain recursively.
   For simplicity we limit recursion depth by the finite set of hashes. *)
Balance(node, acc) ==
    LET
        chain == [h \in Hash |-> IF ledgers[node][h] = NoBlock
                               THEN NoBlock
                               ELSE ledgers[node][h]]
        Rec(h) ==
            IF h = NoHashVal THEN 0
            ELSE
                LET blk == chain[h] IN
                IF blk = NoBlock THEN 0
                ELSE
                    CASE blk.type = "genesis"      -> blk.amount
                     [] blk.type = "send"         -> -blk.amount + Rec(blk.prevHash)
                     [] blk.type = "receive"      -> blk.amount + Rec(blk.prevHash)
                     [] blk.type = "open"         -> blk.amount + Rec(blk.prevHash)
                     [] blk.type = "change"       -> Rec(blk.prevHash)
                     [] OTHER                    -> Rec(blk.prevHash)
    IN Rec(lastHash)

(* ────────────────────────────────────────────────────────────── *)
(* Initial state                                                 *)
(* ────────────────────────────────────────────────────────────── *)

Init ==
    /\ lastHash = NoHashVal
    /\ ledgers = [ n \in Node |-> EmptyLedger ]
    /\ received = [ n \in Node |-> EmptyReceived ]

(* ────────────────────────────────────────────────────────────── *)
(* Actions                                                       *)
(* ────────────────────────────────────────────────────────────── *)

CreateGenesis ==
    /\ \E pk \in PublicKey :
          \E sig \in Nat :
            LET blk ==
                [ type      |-> "genesis",
                  prevHash  |-> NoHashVal,
                  srcHash   |-> NoHashVal,
                  dst       |-> pk,
                  amount    |-> GenesisBalance,
                  rep       |-> pk,
                  signer    |-> pk,
                  signature |-> sig,
                  hash      |-> BlockHash(<< "genesis", NoHashVal, NoHashVal, pk,
                                            GenesisBalance, pk, pk, sig >>) ]
            IN
            /\ lastHash = NoHashVal
            /\ \A n \in Node :
                  /\ ledgers' = [ ledgers EXCEPT ![n][blk.hash] = blk ]
            /\ \A n \in Node : received' = [ received EXCEPT ![n] = {} ]
            /\ lastHash' = blk.hash
            /\ SignatureValid(sig, pk) = TRUE
    /\ UNCHANGED <<>>   \* No other variables change (already captured)

CreateSend(node) ==
    /\ node \in Node
    /\ \E pk \in PublicKey :
         /\ \E amount \in Nat :
              /\ amount <= Balance(node, pk)   \* cannot overdraw
              /\ \E prev \in Hash :
                   ledgers[node][prev] # NoBlock
                   /\ ledgers[node][prev].signer = pk
                   /\ \E sig \in Nat :
                        LET blk ==
                            [ type      |-> "send",
                              prevHash  |-> prev,
                              srcHash   |-> NoHashVal,
                              dst       |-> pk,            \* destination will be filled later
                              amount    |-> amount,
                              rep       |-> NoHash,
                              signer    |-> pk,
                              signature |-> sig,
                              hash      |-> BlockHash(<< "send", prev, NoHashVal,
                                                        pk, amount, NoHash, pk, sig >>) ]
                        IN
                        /\ ledgers' = [ n \in Node |-> IF n = node
                                                   THEN [ ledgers[n] EXCEPT ![blk.hash] = blk ]
                                                   ELSE ledgers[n] ]
                        /\ received' = [ n \in Node |-> IF n # node
                                                    THEN received[n] \cup {blk.hash}
                                                    ELSE received[n] ]
                        /\ lastHash' = blk.hash
                        /\ SignatureValid(sig, pk) = TRUE
    /\ UNCHANGED <<>>    \* other variables unchanged

CreateOpen(node) ==
    /\ node \in Node
    /\ \E sendHash \in Hash :
         /\ ledgers[node][sendHash] # NoBlock
         /\ ledgers[node][sendHash].type = "send"
         /\ ledgers[node][sendHash].dst = pk   \* pk is the public key of this node
         /\ \E pk \in PublicKey :
              /\ pk = pk_of_node(node)   \* function that maps node to its public key
              /\ \E sig \in Nat :
                   LET blk ==
                       [ type      |-> "open",
                         prevHash  |-> NoHashVal,
                         srcHash   |-> sendHash,
                         dst       |-> pk,
                         amount    |-> ledgers[node][sendHash].amount,
                         rep       |-> NoHash,
                         signer    |-> pk,
                         signature |-> sig,
                         hash      |-> BlockHash(<< "open", NoHashVal, sendHash,
                                                   pk, ledgers[node][sendHash].amount,
                                                   NoHash, pk, sig >>) ]
                   IN
                   /\ ledgers' = [ n \in Node |-> IF n = node
                                              THEN [ ledgers[n] EXCEPT ![blk.hash] = blk ]
                                              ELSE ledgers[n] ]
                   /\ received' = [ n \in Node |-> IF n # node
                                                   THEN received[n] \cup {blk.hash}
                                                   ELSE received[n] ]
                   /\ lastHash' = blk.hash
                   /\ SignatureValid(sig, pk) = TRUE
    /\ UNCHANGED <<>>

CreateReceive(node) ==
    /\ node \in Node
    /\ \E sendHash \in Hash :
         /\ ledgers[node][sendHash] # NoBlock
         /\ ledgers[node][sendHash].type = "send"
         /\ \E prev \in Hash :
              /\ ledgers[node][prev] # NoBlock
              /\ ledgers[node][prev].signer = pk_of_node(node)
              /\ \E sig \in Nat :
                   LET blk ==
                       [ type      |-> "receive",
                         prevHash  |-> prev,
                         srcHash   |-> sendHash,
                         dst       |-> pk_of_node(node),
                         amount    |-> ledgers[node][sendHash].amount,
                         rep       |-> NoHash,
                         signer    |-> pk_of_node(node),
                         signature |-> sig,
                         hash      |-> BlockHash(<< "receive", prev, sendHash,
                                                   pk_of_node(node),
                                                   ledgers[node][sendHash].amount,
                                                   NoHash,
                                                   pk_of_node(node), sig >>) ]
                   IN
                   /\ ledgers' = [ n \in Node |-> IF n = node
                                              THEN [ ledgers[n] EXCEPT ![blk.hash] = blk ]
                                              ELSE ledgers[n] ]
                   /\ received' = [ n \in Node |-> IF n # node
                                                   THEN received[n] \cup {blk.hash}
                                                   ELSE received[n] ]
                   /\ lastHash' = blk.hash
                   /\ SignatureValid(sig, pk_of_node(node)) = TRUE
    /\ UNCHANGED <<>>

CreateChange(node) ==
    /\ node \in Node
    /\ \E prev \in Hash :
         /\ ledgers[node][prev] # NoBlock
         /\ \E newRep \in PublicKey :
              /\ \E sig \in Nat :
                   LET blk ==
                       [ type      |-> "change",
                         prevHash  |-> prev,
                         srcHash   |-> NoHashVal,
                         dst       |-> NoHash,
                         amount    |-> 0,
                         rep       |-> newRep,
                         signer    |-> pk_of_node(node),
                         signature |-> sig,
                         hash      |-> BlockHash(<< "change", prev, NoHashVal,
                                                   NoHash, 0, newRep,
                                                   pk_of_node(node), sig >>) ]
                   IN
                   /\ ledgers' = [ n \in Node |-> IF n = node
                                              THEN [ ledgers[n] EXCEPT ![blk.hash] = blk ]
                                              ELSE ledgers[n] ]
                   /\ received' = [ n \in Node |-> IF n # node
                                                   THEN received[n] \cup {blk.hash}
                                                   ELSE received[n] ]
                   /\ lastHash' = blk.hash
                   /\ SignatureValid(sig, pk_of_node(node)) = TRUE
    /\ UNCHANGED <<>>

ProcessReceived(node) ==
    /\ node \in Node
    /\ \E h \in received[node] :
         /\ ledgers[node][h] # NoBlock   \* block already validated on this node
         /\ received' = [ received EXCEPT ![node] = received[node] \ {h} ]
    /\ UNCHANGED <<lastHash, ledgers>>

Next ==
    \/ \E n \in Node : CreateSend(n)
    \/ \E n \in Node : CreateOpen(n)
    \/ \E n \in Node : CreateReceive(n)
    \/ \E n \in Node : CreateChange(n)
    \/ \E n \in Node : ProcessReceived(n)
    \/ CreateGenesis
    \/ UNCHANGED <<lastHash, ledgers, received>>

Spec == Init /\ [][Next]_<<lastHash, ledgers, received>>

(* ────────────────────────────────────────────────────────────── *)
(* Invariants                                                    *)
(* ────────────────────────────────────────────────────────────── *)

TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledgers \in [Node -> [Hash -> (BlockRecord \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
       \A h \in Hash :
          IF ledgers[n][h] # NoBlock
          THEN SignatureValid(ledgers[n][h].signature, ledgers[n][h].signer)
          ELSE TRUE

====