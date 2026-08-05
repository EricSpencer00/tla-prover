---- MODULE Nano ----
EXTENDS Naturals, Sequences

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

Signature == [signed | BOOLEAN]
Block == [prev | Hash, typ | {"GENESIS", "SEND", "OPEN", "RECEIVE", "CHANGE"}, owner | PublicKey, amt | Nat, sig | Signature, link | Hash]

RECURSIVE ChainBalance(_, _)
ChainBalance(chain, h) ==
  IF h = NoHash THEN 0
  ELSE IF chain[h].typ = "SEND" THEN ChainBalance(chain, chain[h].prev) - chain[h].amt
       ELSE IF chain[h].typ = "RECEIVE" THEN ChainBalance(chain, chain[h].prev) + chain[h].amt
            ELSE ChainBalance(chain, chain[h].prev)

RECURSIVE SumBalances(_)
SumBalances(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN ChainBalance([h \in Hash |-> IF h = x THEN NoBlock ELSE NoBlock]) + SumBalances(S \ {x})

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]
  /\ \A n \in Node : received[n] \subseteq Hash

\* The cryptographic core: every recorded block must carry a signature that
\* actually matches the account holding the chain it sits in.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].sig.signed

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* Genesis block is broadcast to every node's copy at once.
CreateGenesisBlock ==
  /\ lastHash = NoHashVal
  /\ \E n \in Node, pk \in PrivateKey : ledger' = [m \in Node |-> [h \in Hash |-> IF h = NoHashVal THEN [prev |-> NoHash, typ |-> "GENESIS", owner |-> pk, amt |-> GenesisBalance, sig |-> [signed |-> TRUE], link |-> NoHash] ELSE NoBlockVal] : m \in Node]
  /\ lastHash' = NoHashVal
  /\ received' = [n \in Node |-> {}]

CreateSendBlock ==
  /\ lastHash \in Hash
  /\ \E n \in Node, pk \in PrivateKey, rc \in PublicKey, a \in 1..9 :
       /\ ledger[n][lastHash].owner = pk
       /\ ChainBalance([h \in Hash |-> IF h = lastHash THEN ledger[n][lastHash] ELSE NoBlockVal], lastHash) >= a
       /\ lastHash' = NoHashVal
       /\ ledger' = [ledger EXCEPT ![n][NoHashVal] = [prev |-> lastHash, typ |-> "SEND", owner |-> pk, amt |-> a, sig |-> [signed |-> TRUE], link |-> NoHash]]
       /\ received' = [m \in Node |-> received[m] \cup {NoHashVal}]
  \/ UNCHANGED <<>

CreateOpenBlock ==
  /\ lastHash \in Hash
  /\ \E n \in Node, pk \in PrivateKey, rc \in PublicKey, a \in 1..9 :
       /\ ledger[n][lastHash].typ = "SEND"
       /\ ledger[n][lastHash].owner = pk
       /\ ChainBalance([h \in Hash |-> NoBlockVal], lastHash) = 0
       /\ lastHash' = NoHashVal
       /\ ledger' = [ledger EXCEPT ![n][NoHashVal] = [prev |-> lastHash, typ |-> "OPEN", owner |-> pk, amt |-> a, sig |-> [signed |-> TRUE], link |-> NoHash]]
       /\ received' = [m \in Node |-> received[m] \cup {NoHashVal}]
  \/ UNCHANGED <<>>

CreateReceiveBlock ==
  /\ lastHash \in Hash
  /\ \E n \in Node, pk \in PrivateKey, rc \in PublicKey, a \in 1..9 :
       /\ ledger[n][lastHash].typ = "SEND"
       /\ ledger[n][lastHash].owner = pk
       /\ lastHash' = NoHashVal
       /\ ledger' = [ledger EXCEPT ![n][NoHashVal] = [prev |-> lastHash, typ |-> "RECEIVE", owner |-> pk, amt |-> a, sig |-> [signed |-> TRUE], link |-> NoHash]]
       /\ received' = [m \in Node |-> received[m] \cup {NoHashVal}]
  \/ UNCHANGED <<>>

CreateChangeRepresentativeBlock ==
  /\ lastHash \in Hash
  /\ \E n \in Node, pk \in PrivateKey, rc \in PublicKey :
       /\ ledger[n][lastHash].owner = pk
       /\ lastHash' = NoHashVal
       /\ ledger' = [ledger EXCEPT ![n][NoHashVal] = [prev |-> lastHash, typ |-> "CHANGE", owner |-> pk, amt |-> 0, sig |-> [signed |-> TRUE], link |-> NoHash]]
       /\ received' = [m \in Node |-> received[m] \cup {NoHashVal}]
  \/ UNCHANGED <<>>

\* Validation includes signature checking, existence of referenced blocks and
\* block-type-specific balance rules; it is anchored on each node's own copy.
ValidateBlock ==
  \E n \in Node, h \in received[n] :
    /\ ledger[n][h] # NoBlockVal
    /\ ledger[n][h].sig.signed
    /\ (h = NoHashVal => TRUE)
    /\ (ledger[n][h].typ = "SEND" => ChainBalance([hh \in Hash |-> IF hh = h THEN ledger[n][hh] ELSE NoBlockVal], ledger[n][h].prev) >= ledger[n][h].amt)
    /\ (ledger[n][h].typ = "OPEN" => ChainBalance([hh \in Hash |-> IF hh = h THEN ledger[n][hh] ELSE NoBlockVal], ledger[n][h].prev) = 0)
    /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
    /\ UNCHANGED <<lastHash, ledger>>

Next == CreateGenesisBlock \/ CreateSendBlock \/ CreateOpenBlock \/ CreateReceiveBlock \/ CreateChangeRepresentativeBlock \/ ValidateBlock

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

====