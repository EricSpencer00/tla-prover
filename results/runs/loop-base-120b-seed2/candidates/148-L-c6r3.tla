---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node,
    GenesisBalance, NoBlockVal, CalculateHash,
    (* additional constants for key ownership *)
    OwnedKey, PrivToPub,
    (* identifiers required by the configuration *)
    NoHash, NoBlock

(* ------------------------------------------------------------------------- *)
(* Types *)

Block ==
    [ hash       : Hash,
      prevHash   : Hash,
      account    : PublicKey,
      type       : {"genesis", "send", "receive", "open", "change"},
      amount     : Nat,
      recipient  : PublicKey \cup {NoHashVal},
      signature  : PrivateKey ]

BlockUnion == Block \cup { NoBlockVal }

(* ------------------------------------------------------------------------- *)
(* Variables *)

VARIABLES
    lastHash,            \* the most recent block hash
    ledger,              \* map from hashes to blocks (or NoBlockVal)
    received,            \* per‑node set of hashes that have been broadcast but not yet processed
    balances             \* current balance of each public key

(* ------------------------------------------------------------------------- *)
(* Helper operators *)

ValidSignature(b) ==
    b.signature = b.account

CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

(* ------------------------------------------------------------------------- *)
(* Initialization *)

Init ==
    /\ lastHash = NoHashVal
    /\ ledger   = [h \in Hash |-> NoBlockVal]
    /\ received = [n \in Node |-> {}]
    /\ balances = [pk \in PublicKey |-> 0]

(* ------------------------------------------------------------------------- *)
(* Actions *)

(* Create the unique genesis block *)
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E n \in Node :
        LET pk      == PrivToPub[OwnedKey[n]]
            newHash == CalculateHashImpl(
                         [type      |-> "genesis",
                          account   |-> pk,
                          amount    |-> GenesisBalance,
                          prevHash  |-> NoHashVal,
                          recipient |-> NoHashVal,
                          signature |-> OwnedKey[n]],
                         NoHashVal)
        IN
        /\ newHash # NoHashVal
        /\ lastHash' = newHash
        /\ ledger'   = [ledger EXCEPT ![newHash] =
                         [hash       |-> newHash,
                          prevHash   |-> NoHashVal,
                          account    |-> pk,
                          type       |-> "genesis",
                          amount     |-> GenesisBalance,
                          recipient  |-> NoHashVal,
                          signature  |-> OwnedKey[n]]]
        /\ received' = [n2 \in Node |-> received[n2] \cup {newHash}]
        /\ balances' = [balances EXCEPT ![pk] = GenesisBalance]
        /\ UNCHANGED <<>>

(* Create a send block *)
CreateSend ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node, amt \in Nat, rec \in PublicKey :
        LET pk      == PrivToPub[OwnedKey[n]]
            prev    == lastHash
            newHash == CalculateHashImpl(
                         [type      |-> "send",
                          account   |-> pk,
                          amount    |-> amt,
                          prevHash  |-> prev,
                          recipient |-> rec,
                          signature |-> OwnedKey[n]],
                         prev)
        IN
        /\ balances[pk] >= amt
        /\ ledger[newHash] = NoBlockVal
        /\ lastHash' = newHash
        /\ ledger'   = [ledger EXCEPT ![newHash] =
                         [hash       |-> newHash,
                          prevHash   |-> prev,
                          account    |-> pk,
                          type       |-> "send",
                          amount     |-> amt,
                          recipient  |-> rec,
                          signature  |-> OwnedKey[n]]]
        /\ received' = [n2 \in Node |-> received[n2] \cup {newHash}]
        /\ balances' = [balances EXCEPT ![pk] = balances[pk] - amt]
        /\ UNCHANGED <<>>

(* Create a receive block that claims a previously sent amount *)
CreateReceive ==
    /\ \E n \in Node, sh \in Hash :
        LET pk   == PrivToPub[OwnedKey[n]]
            amt   == ledger[sh].amount
            prev  == lastHash
            newHash == CalculateHashImpl(
                         [type      |-> "receive",
                          account   |-> pk,
                          amount    |-> amt,
                          prevHash  |-> prev,
                          recipient |-> NoHashVal,
                          signature |-> OwnedKey[n]],
                         prev)
        IN
        /\ sh \in received[n]
        /\ ledger[sh] # NoBlockVal
        /\ ledger[sh].type = "send"
        /\ ledger[sh].recipient = pk
        /\ ledger[newHash] = NoBlockVal
        /\ lastHash' = newHash
        /\ ledger'   = [ledger EXCEPT ![newHash] =
                         [hash       |-> newHash,
                          prevHash   |-> prev,
                          account    |-> pk,
                          type       |-> "receive",
                          amount     |-> amt,
                          recipient  |-> NoHashVal,
                          signature  |-> OwnedKey[n]]]
        /\ received' = [n2 \in Node |-> IF n2 = n THEN received[n2] \ {sh} ELSE received[n2]]
        /\ balances' = [balances EXCEPT ![pk] = balances[pk] + amt]
        /\ UNCHANGED <<>>

(* Open a new account using a received send block *)
CreateOpen ==
    /\ \E n \in Node, sh \in Hash :
        LET pk   == PrivToPub[OwnedKey[n]]
            amt   == ledger[sh].amount
            newHash == CalculateHashImpl(
                         [type      |-> "open",
                          account   |-> pk,
                          amount    |-> amt,
                          prevHash  |-> NoHashVal,
                          recipient |-> NoHashVal,
                          signature |-> OwnedKey[n]],
                         NoHashVal)
        IN
        /\ sh \in received[n]
        /\ ledger[sh] # NoBlockVal
        /\ ledger[sh].type = "send"
        /\ ledger[sh].recipient = pk
        /\ ledger[newHash] = NoBlockVal
        /\ lastHash' = newHash
        /\ ledger'   = [ledger EXCEPT ![newHash] =
                         [hash       |-> newHash,
                          prevHash   |-> NoHashVal,
                          account    |-> pk,
                          type       |-> "open",
                          amount     |-> amt,
                          recipient  |-> NoHashVal,
                          signature  |-> OwnedKey[n]]]
        /\ received' = [n2 \in Node |-> IF n2 = n THEN received[n2] \ {sh} ELSE received[n2]]
        /\ balances' = [balances EXCEPT ![pk] = amt]
        /\ UNCHANGED <<>>

(* Change the voting representative for an account *)
CreateChange ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node, rep \in PublicKey :
        LET pk      == PrivToPub[OwnedKey[n]]
            prev    == lastHash
            newHash == CalculateHashImpl(
                         [type      |-> "change",
                          account   |-> pk,
                          amount    |-> 0,
                          prevHash  |-> prev,
                          recipient |-> rep,
                          signature |-> OwnedKey[n]],
                         prev)
        IN
        /\ ledger[newHash] = NoBlockVal
        /\ lastHash' = newHash
        /\ ledger'   = [ledger EXCEPT ![newHash] =
                         [hash       |-> newHash,
                          prevHash   |-> prev,
                          account    |-> pk,
                          type       |-> "change",
                          amount     |-> 0,
                          recipient  |-> rep,
                          signature  |-> OwnedKey[n]]]
        /\ received' = [n2 \in Node |-> received[n2] \cup {newHash}]
        /\ UNCHANGED <<balances>>

(* ------------------------------------------------------------------------- *)
(* Next-state relation *)

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateReceive
    \/ CreateOpen
    \/ CreateChange

(* ------------------------------------------------------------------------- *)
(* Specification *)

Spec == Init /\ [][Next]_<<lastHash, ledger, received, balances>>

(* ------------------------------------------------------------------------- *)
(* Invariants *)

TypeInvariant ==
    /\ lastHash \in Hash \/ lastHash = NoHashVal
    /\ ledger   \in [Hash -> BlockUnion]
    /\ received \in [Node -> SUBSET Hash]
    /\ balances \in [PublicKey -> Nat]

SafetyInvariant ==
    \A h \in Hash :
        IF ledger[h] # NoBlockVal
        THEN ValidSignature(ledger[h])
        ELSE TRUE

====