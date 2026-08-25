---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Hash, NoHashVal,
    PrivateKey, PublicKey,
    Node,
    GenesisBalance,
    NoBlockVal,
    CalculateHash,
    NoHash,
    NoBlock

(* Sentinels *)
ASSUME NoHash = NoHashVal
ASSUME NoBlock = NoBlockVal

(* A dummy public key used for fields that are not relevant for a given block type *)
DummyPub == CHOOSE p \in PublicKey : TRUE

(* Mapping from a private key to its public key (abstract) *)
PrivateToPublic == [sk \in PrivateKey |-> CHOOSE pk \in PublicKey : TRUE]

(* Block record definition *)
Block ==
    [type          : {"genesis","send","open","receive","change"},
     prev          : Hash \cup {NoHash},
     account       : PublicKey,
     signer        : PublicKey,
     amount        : Nat,
     destination   : PublicKey,
     representative: PublicKey,
     sig           : PublicKey]

(* Simple signature validation: the signature field must equal the signer's public key,
   and the signer must be the account that owns the block. *)
SignatureValid(b) ==
    /\ b.sig = b.signer
    /\ b.signer = b.account

(* Abstract hash calculation implementation used for model checking *)
CalculateHashImpl(data, prev) == CHOOSE h \in Hash : TRUE

(* Variables *)
VARIABLES
    lastHash,
    ledger,
    received,
    genesisCreated

(*----------------------------------------------------------------------*)
(* Initial state *)
Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]
    /\ genesisCreated = FALSE

(*----------------------------------------------------------------------*)
(* Helper to compute balance by walking an account chain *)
Balance(node, h) ==
    IF h = NoHash THEN 0
    ELSE
        LET b == ledger[node][h] IN
        IF b = NoBlock THEN 0
        ELSE
            CASE b.type = "genesis"   -> b.amount
               [] b.type = "send"     -> Balance(node, b.prev) - b.amount
               [] b.type = "receive"  -> Balance(node, b.prev) + b.amount
               [] b.type = "open"     -> b.amount
               [] b.type = "change"   -> Balance(node, b.prev)
               [] OTHER               -> 0

(*----------------------------------------------------------------------*)
(* Action: create the genesis block (once) *)
CreateGenesis ==
    /\ ~genesisCreated
    /\ \E pk \in PublicKey :
        \E sk \in PrivateKey :
            PrivateToPublic[sk] = pk
            /\ LET gBlock ==
                    [type          |-> "genesis",
                     prev          |-> NoHash,
                     account       |-> pk,
                     signer        |-> pk,
                     amount        |-> GenesisBalance,
                     destination   |-> DummyPub,
                     representative|-> DummyPub,
                     sig           |-> pk] IN
               newHash == CalculateHash(gBlock, NoHash)
               /\ lastHash' = newHash
               /\ ledger' = [n \in Node |-> 
                               [h \in Hash |-> IF h = newHash THEN gBlock ELSE ledger[n][h]]]
               /\ received' = [n \in Node |-> {}]
               /\ genesisCreated' = TRUE
    /\ UNCHANGED <<>>

(*----------------------------------------------------------------------*)
(* Action: create a send block *)
CreateSend ==
    /\ genesisCreated
    /\ \E sender \in Node :
        \E sk \in PrivateKey :
            \E pk \in PublicKey :
                PrivateToPublic[sk] = pk
                /\ \E prevHash \in Hash :
                    ledger[sender][prevHash] # NoBlock
                    /\ ledger[sender][prevHash].account = pk
                    /\ \E amt \in Nat :
                        amt <= Balance(sender, prevHash)
                        /\ \E destPub \in PublicKey :
                            LET sBlock ==
                                [type          |-> "send",
                                 prev          |-> prevHash,
                                 account       |-> pk,
                                 signer        |-> pk,
                                 amount        |-> amt,
                                 destination   |-> destPub,
                                 representative|-> DummyPub,
                                 sig           |-> pk] IN
                            newHash == CalculateHash(sBlock, prevHash)
                            /\ lastHash' = newHash
                            /\ ledger' = [n \in Node |-> 
                                            [h \in Hash |-> IF h = newHash THEN sBlock ELSE ledger[n][h]]]
                            /\ received' = [n \in Node |-> received[n] \cup {newHash}]
                            /\ UNCHANGED <<genesisCreated>>
    /\ UNCHANGED <<>>

(*----------------------------------------------------------------------*)
(* Action: process a received block at a node *)
ProcessBlock ==
    /\ \E n \in Node :
        \E h \in received[n] :
            LET b == ledger[n][h] IN
            /\ b # NoBlock
            /\ SignatureValid(b)
            /\ ledger' = [m \in Node |-> 
                            IF m = n THEN
                                [hh \in Hash |-> IF hh = h THEN b ELSE ledger[m][hh]]
                            ELSE ledger[m]]
            /\ received' = [m \in Node |-> 
                              IF m = n THEN received[m] \setminus {h}
                              ELSE received[m]]
            /\ UNCHANGED <<lastHash, genesisCreated>>
    /\ UNCHANGED <<>>

(*----------------------------------------------------------------------*)
(* Next-state relation *)
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ ProcessBlock

(*----------------------------------------------------------------------*)
(* Specification *)
Spec == Init /\ [][Next]_<<lastHash, ledger, received, genesisCreated>>

(*----------------------------------------------------------------------*)
(* Invariants *)
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET b == ledger[n][h] IN
            b # NoBlock => SignatureValid(b)

====