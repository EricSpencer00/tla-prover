---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Hash, NoHash, NoHashVal,
    PrivateKey, PublicKey, Node,
    GenesisBalance,
    NoBlock, NoBlockVal,
    CalculateHash

(* Implementation of the abstract hash calculation; the .cfg may substitute
   CalculateHash with CalculateHashImpl. *)
CalculateHashImpl(b, ph) == 
    CHOOSE h \in Hash : TRUE

(* Mapping from private keys to their public keys. *)
PrivToPub \in [PrivateKey -> PublicKey]

(* Mapping from each node to the private key it owns. *)
NodePriv \in [Node -> PrivateKey]

(* Definition of a block record. *)
Block == [type            : {"Genesis","Send","Open","Receive","Change"},
          prev            : Hash,
          account         : PublicKey,
          amount          : Nat,
          destination     : PublicKey,
          source          : Hash,
          representative  : PublicKey,
          signature       : STRING]

(* Sentinel block value representing the absence of a block. *)
NoBlockVal ==
    [type           |-> "NoBlock",
     prev           |-> NoHashVal,
     account        |-> [<<>>],
     amount         |-> 0,
     destination    |-> [<<>>],
     source         |-> NoHashVal,
     representative|-> [<<>>],
     signature      |-> ""]

VARIABLES
    lastHash,
    ledger,
    received

(* Initial state. *)
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [h \in Hash |-> NoBlockVal]
    /\ received = [n \in Node |-> {}]

(* Retrieve the private key that corresponds to a public key. *)
OwnerPriv(pk) ==
    CHOOSE pkv \in PrivateKey : PrivToPub[pkv] = pk

(* Abstract signing function. *)
Sign(pk, blk) == <<pk, blk>>

(* Check that a block's signature matches its owner's private key. *)
ValidSignature(b) ==
    b.signature = Sign(OwnerPriv(b.account), b)

(* Abstract balance function; in a concrete model this would walk the account
   chain. *)
Balance(pub, l) == CHOOSE bal \in Nat : TRUE

(* Validation of a block before a node can accept it. *)
ValidateBlock(node, h) ==
    LET b == ledger[h] IN
    /\ b # NoBlockVal
    /\ ValidSignature(b)
    /\ CASE b.type = "Genesis" -> TRUE
            [] b.type = "Send" ->
               /\ b.prev # NoHashVal
               /\ Balance(b.account, ledger) >= b.amount
            [] b.type = "Open" ->
               /\ b.prev = NoHashVal
               /\ TRUE
            [] b.type = "Receive" ->
               /\ b.prev # NoHashVal
               /\ b.source # NoHashVal
            [] b.type = "Change" ->
               /\ b.prev # NoHashVal
        OTHER -> FALSE

(* Action: create the genesis block. *)
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E n \in Node :
          LET pk == PrivToPub[NodePriv[n]]
              b  == [type           |-> "Genesis",
                    prev           |-> NoHashVal,
                    account        |-> pk,
                    amount         |-> GenesisBalance,
                    destination    |-> [<<>>],
                    source         |-> NoHashVal,
                    representative|-> [<<>>],
                    signature      |-> Sign(NodePriv[n], <<pk, GenesisBalance>>)]
              h  == CalculateHash(b, NoHashVal)
          IN
              /\ h \in Hash
              /\ lastHash' = h
              /\ ledger' = [h2 \in Hash |-> IF h2 = h THEN b ELSE ledger[h2]]
              /\ received' = [n2 \in Node |-> received[n2] \cup {h}]
    /\ UNCHANGED <<>>

(* Action: create a send block. *)
CreateSend ==
    \E n \in Node :
        LET pk        == PrivToPub[NodePriv[n]]
            prevHash  == lastHash
            amt       == 1                         \* abstract amount
            dest      == CHOOSE d \in PublicKey : d # pk
            b         == [type           |-> "Send",
                         prev           |-> prevHash,
                         account        |-> pk,
                         amount         |-> amt,
                         destination    |-> dest,
                         source         |-> NoHashVal,
                         representative|-> [<<>>],
                         signature      |-> Sign(NodePriv[n], <<pk, prevHash, amt, dest>>)]
            h         == CalculateHash(b, prevHash)
        IN
            /\ Balance(pk, ledger) >= amt
            /\ lastHash' = h
            /\ ledger' = [h2 \in Hash |-> IF h2 = h THEN b ELSE ledger[h2]]
            /\ received' = [n2 \in Node |-> received[n2] \cup {h}]
    /\ UNCHANGED <<>>

(* Action: create an open block for a new account. *)
CreateOpen ==
    \E n \in Node :
        LET pk          == PrivToPub[NodePriv[n]]
            sourceHash  == CHOOSE sh \in Hash :
                              ledger[sh].type = "Send" /\ ledger[sh].destination = pk
            b           == [type           |-> "Open",
                           prev           |-> NoHashVal,
                           account        |-> pk,
                           amount         |-> ledger[sourceHash].amount,
                           destination    |-> [<<>>],
                           source         |-> sourceHash,
                           representative|-> [<<>>],
                           signature      |-> Sign(NodePriv[n], <<pk, sourceHash>>)]
            h           == CalculateHash(b, NoHashVal)
        IN
            /\ lastHash' = h
            /\ ledger' = [h2 \in Hash |-> IF h2 = h THEN b ELSE ledger[h2]]
            /\ received' = [n2 \in Node |-> received[n2] \cup {h}]
    /\ UNCHANGED <<>>

(* Action: create a receive block to claim a pending send. *)
CreateReceive ==
    \E n \in Node :
        LET pk          == PrivToPub[NodePriv[n]]
            prevHash    == lastHash
            sourceHash  == CHOOSE sh \in Hash :
                              ledger[sh].type = "Send" /\ ledger[sh].destination = pk
            b           == [type           |-> "Receive",
                           prev           |-> prevHash,
                           account        |-> pk,
                           amount         |-> ledger[sourceHash].amount,
                           destination    |-> [<<>>],
                           source         |-> sourceHash,
                           representative|-> [<<>>],
                           signature      |-> Sign(NodePriv[n], <<pk, prevHash, sourceHash>>)]
            h           == CalculateHash(b, prevHash)
        IN
            /\ lastHash' = h
            /\ ledger' = [h2 \in Hash |-> IF h2 = h THEN b ELSE ledger[h2]]
            /\ received' = [n2 \in Node |-> received[n2] \cup {h}]
    /\ UNCHANGED <<>>

(* Action: create a change representative block. *)
CreateChange ==
    \E n \in Node :
        LET pk          == PrivToPub[NodePriv[n]]
            prevHash    == lastHash
            newRep      == CHOOSE r \in PublicKey : r # pk
            b           == [type           |-> "Change",
                           prev           |-> prevHash,
                           account        |-> pk,
                           amount         |-> 0,
                           destination    |-> [<<>>],
                           source         |-> NoHashVal,
                           representative|-> newRep,
                           signature      |-> Sign(NodePriv[n], <<pk, prevHash, newRep>>)]
            h           == CalculateHash(b, prevHash)
        IN
            /\ lastHash' = h
            /\ ledger' = [h2 \in Hash |-> IF h2 = h THEN b ELSE ledger[h2]]
            /\ received' = [n2 \in Node |-> received[n2] \cup {h}]
    /\ UNCHANGED <<>>

(* Action: a node processes a received block. *)
ProcessBlock ==
    \E n \in Node :
        \E h \in received[n] :
            LET b == ledger[h] IN
            /\ b # NoBlockVal
            /\ ValidateBlock(n, h)
            /\ ledger' = ledger
            /\ received' = [n2 \in Node |-> IF n2 = n THEN received[n2] \ {h}
                                          ELSE received[n2]]
    /\ UNCHANGED lastHash

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

(* Type invariant: variables stay within their declared types. *)
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Hash -> Block]
    /\ received \in [Node -> SUBSET Hash]

(* Safety invariant: every stored block has a valid signature. *)
SafetyInvariant ==
    \A h \in Hash :
        LET b == ledger[h] IN
        IF b = NoBlockVal THEN TRUE ELSE ValidSignature(b)

====