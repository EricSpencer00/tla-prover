---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Hash,               \* Universe of possible hash values
    NoHashVal,          \* Sentinel value indicating no hash
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,    \* Total supply created in the genesis block
    NoBlockVal,         \* Sentinel value indicating absence of a block
    CalculateHash,      \* Abstract hash operator (will be overridden)
    NoHash,             \* Another sentinel for “no hash”
    NoBlock             \* Another sentinel for “no block”

(* ------------------------------------------------------------------------
   Additional auxiliary constants (not required by the .cfg but useful)
   ------------------------------------------------------------------------ *)
CONSTANTS
    PubKeyOf \in [PrivateKey -> PublicKey],   \* mapping private → public key
    Sig      \in [PRIVATEKEY -> {}}           \* abstract signature space
    SignOf   \in [PrivateKey -> Sig]          \* signature produced by a private key

(* ------------------------------------------------------------------------
   Block record definition
   ------------------------------------------------------------------------ *)
Block ==
    [type        : {"Genesis","Send","Open","Receive","Change"},
     prev        : Hash,               \* previous block hash in the account chain
     signer      : PrivateKey,         \* private key that signed the block
     signature   : Sig,                \* the signature
     amount      : Nat,                \* amount transferred (if applicable)
     dest        : PublicKey,          \* destination account (for send)
     source      : Hash,               \* source send block (for open/receive)
     rep         : PublicKey]          \* voting representative (for change)

(* ------------------------------------------------------------------------
   Variables
   ------------------------------------------------------------------------ *)
VARIABLES
    lastHash,          \* the most recent block hash created in the system
    ledger,            \* per‑node copy of the distributed ledger
    received           \* per‑node set of hashes received but not yet processed

(* ------------------------------------------------------------------------
   Helper definitions
   ------------------------------------------------------------------------ *)

(* Abstract hash calculation – will be substituted by CalculateHashImpl
      in the .cfg file.  Here we give a simple nondeterministic definition
      that picks any element of Hash. *)
CalculateHashImpl(b, prev) ==
    CHOOSE h \in Hash : TRUE

(* Signature verification – abstracted.  For the purpose of the invariant
   we simply require the signature to be the one derived from the signer. *)
VerifySignature(sig, pk, blk) ==
    sig = SignOf[blk.signer] /\ pk = PubKeyOf[blk.signer]

(* The sentinel values are identified with the supplied constants *)
NoHash == NoHashVal
NoBlock == NoBlockVal

(* ------------------------------------------------------------------------
   Initial state
   ------------------------------------------------------------------------ *)
Init ==
    /\ lastHash = NoHash
    /\ ledger   = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

(* ------------------------------------------------------------------------
   Actions
   ------------------------------------------------------------------------ *)

Genesis ==
    /\ lastHash = NoHash
    /\ \E n \in Node, pk \in PrivateKey, h \in Hash :
        LET blk == [type      |-> "Genesis",
                    prev      |-> NoHash,
                    signer    |-> pk,
                    signature |-> SignOf[pk],
                    amount    |-> GenesisBalance,
                    dest      |-> NoHash,
                    source    |-> NoHash,
                    rep       |-> NoHash] IN
        /\ h = CalculateHashImpl(blk, NoHash)
        /\ ledger'   = [m \in Node |-> [h2 \in Hash |-> IF h2 = h THEN blk ELSE ledger[m][h2]]]
        /\ received' = [m \in Node |-> received[m] \cup {h}]
        /\ lastHash' = h
        /\ UNCHANGED <<>>

CreateSend ==
    /\ lastHash # NoHash
    /\ \E n \in Node, pk \in PrivateKey, amt \in Nat, dst \in PublicKey,
            hPrev \in Hash, hNew \in Hash :
        LET prevBlk == ledger[n][hPrev] IN
        /\ prevBlk # NoBlock
        /\ prevBlk.type \in {"Genesis","Send","Receive","Change"}
        /\ (* balance check omitted – abstracted *)
        LET blk == [type      |-> "Send",
                    prev      |-> hPrev,
                    signer    |-> pk,
                    signature |-> SignOf[pk],
                    amount    |-> amt,
                    dest      |-> dst,
                    source    |-> NoHash,
                    rep       |-> NoHash] IN
        /\ hNew = CalculateHashImpl(blk, hPrev)
        /\ ledger'   = [m \in Node |-> [h2 \in Hash |-> IF h2 = hNew THEN blk ELSE ledger[m][h2]]]
        /\ received' = [m \in Node |-> received[m] \cup {hNew}]
        /\ lastHash' = hNew
        /\ UNCHANGED <<>>

CreateOpen ==
    /\ lastHash # NoHash
    /\ \E n \in Node, pk \in PrivateKey, srcHash \in Hash,
            hNew \in Hash :
        LET srcBlk == ledger[n][srcHash] IN
        /\ srcBlk # NoBlock
        /\ srcBlk.type = "Send"
        /\ srcBlk.dest = PubKeyOf[pk]   \* send is addressed to this account
        LET blk == [type      |-> "Open",
                    prev      |-> NoHash,
                    signer    |-> pk,
                    signature |-> SignOf[pk],
                    amount    |-> srcBlk.amount,
                    dest      |-> NoHash,
                    source    |-> srcHash,
                    rep       |-> NoHash] IN
        /\ hNew = CalculateHashImpl(blk, NoHash)
        /\ ledger'   = [m \in Node |-> [h2 \in Hash |-> IF h2 = hNew THEN blk ELSE ledger[m][h2]]]
        /\ received' = [m \in Node |-> received[m] \cup {hNew}]
        /\ lastHash' = hNew
        /\ UNCHANGED <<>>

CreateReceive ==
    /\ lastHash # NoHash
    /\ \E n \in Node, pk \in PrivateKey, hPrev \in Hash,
            srcHash \in Hash, hNew \in Hash :
        LET prevBlk == ledger[n][hPrev] IN
        /\ prevBlk # NoBlock
        /\ prevBlk.type \in {"Open","Receive","Change"}
        LET srcBlk == ledger[n][srcHash] IN
        /\ srcBlk # NoBlock
        /\ srcBlk.type = "Send"
        /\ srcBlk.dest = PubKeyOf[pk]
        LET blk == [type      |-> "Receive",
                    prev      |-> hPrev,
                    signer    |-> pk,
                    signature |-> SignOf[pk],
                    amount    |-> srcBlk.amount,
                    dest      |-> NoHash,
                    source    |-> srcHash,
                    rep       |-> NoHash] IN
        /\ hNew = CalculateHashImpl(blk, hPrev)
        /\ ledger'   = [m \in Node |-> [h2 \in Hash |-> IF h2 = hNew THEN blk ELSE ledger[m][h2]]]
        /\ received' = [m \in Node |-> received[m] \cup {hNew}]
        /\ lastHash' = hNew
        /\ UNCHANGED <<>>

CreateChange ==
    /\ lastHash # NoHash
    /\ \E n \in Node, pk \in PrivateKey, hPrev \in Hash,
            newRep \in PublicKey, hNew \in Hash :
        LET prevBlk == ledger[n][hPrev] IN
        /\ prevBlk # NoBlock
        /\ prevBlk.type \in {"Genesis","Send","Open","Receive","Change"}
        LET blk == [type      |-> "Change",
                    prev      |-> hPrev,
                    signer    |-> pk,
                    signature |-> SignOf[pk],
                    amount    |-> 0,
                    dest      |-> NoHash,
                    source    |-> NoHash,
                    rep       |-> newRep] IN
        /\ hNew = CalculateHashImpl(blk, hPrev)
        /\ ledger'   = [m \in Node |-> [h2 \in Hash |-> IF h2 = hNew THEN blk ELSE ledger[m][h2]]]
        /\ received' = [m \in Node |-> received[m] \cup {hNew}]
        /\ lastHash' = hNew
        /\ UNCHANGED <<>>

ProcessReceived ==
    /\ \E n \in Node, h \in received[n] :
        LET blk == ledger[n][h] IN
        /\ blk # NoBlock
        /\ VerifySignature(blk.signature, PubKeyOf[blk.signer], blk)
        /\ ledger'   = ledger
        /\ received' = [m \in Node |-> IF m = n THEN received[m] \ {h} ELSE received[m]]
        /\ UNCHANGED <<lastHash>>

Next ==
    \/ Genesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessReceived

(* ------------------------------------------------------------------------
   Specification
   ------------------------------------------------------------------------ *)
Spec ==
    Init /\ [][Next]_<<lastHash, ledger, received>>

(* ------------------------------------------------------------------------
   Invariants
   ------------------------------------------------------------------------ *)

TypeInvariant ==
    /\ lastHash \in Hash \/ lastHash = NoHash
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            IF ledger[n][h] # NoBlock THEN
                LET blk == ledger[n][h] IN
                    VerifySignature(blk.signature, PubKeyOf[blk.signer], blk)
            ELSE TRUE

====