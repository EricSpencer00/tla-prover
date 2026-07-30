---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME /\ NoHashVal \notin Hash
         /\ NoHash \in Hash
         /\ NoBlockVal \in Hash
         /\ NoBlock \in Hash

VARIABLES lastHash, ledger, recvd
vars == <<lastHash, ledger, recvd>>

Blocks == {NoBlockVal} \cup Hash

\* Compute a chain's balance recursively: walk back from the head block, and
\* each block's type (+send amount, -receive amount) contributes to the total.
RECURSIVE ChainBalance(_, _)
ChainBalance(n, h) ==
  IF h = NoHashVal THEN 0
  ELSE IF h = NoBlockVal THEN 0
  ELSE
    LET blk == ledger[n][h] IN
      ChainBalance(n, blk.prevHash) + blk.amt

Balance == [n \in Node |-> ChainBalance(n, lastHash)]

TypeOK ==
  /\ lastHash \in Hash
  /\ ledger \in [Node -> [Hash -> [hash: Hash, pubKey: PublicKey,
                                   prevHash: Hash, amt: 0..GenesisBalance]]]
  /\ recvd \in [Node -> SUBSET Hash]

\* A signature is valid iff the hash it covers is the hash it claims to cover,
\* and the key that signed it is the public key of the account chain it lives in.
SignatureValid(n, h) ==
  /\ ledger[n][h].hash = h
  /\ ledger[n][h].pubKey = ledger[n][ledger[n][h].prevHash].pubKey

\* The full safety invariant: every block held by every node is a validly signed
\* continuation of the chain it lives in.
SafetyInvariant == \A n \in Node, h \in Hash : SignatureValid(n, h)

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> [hash |-> NoHashVal,
                                               pubKey |-> NoBlockVal,
                                               prevHash |-> NoHashVal,
                                               amt |-> 0]]]
  /\ recvd = [n \in Node |-> {}]

\* Broadcast: a block is delivered to all nodes' in-transit sets together.
Broadcast(h) == [n \in Node |-> recvd[n] \cup {h}]

\* The genesis block is the only one whose prevHash is the sentinel NoHashVal.
CreateGenesisBlock(n, k) ==
  /\ lastHash = NoHash
  /\ lastHash' = CalculateHash([pubKey |-> k, prevHash |-> NoHashVal, amt |-> GenesisBalance])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
        [hash |-> lastHash', pubKey |-> k, prevHash |-> NoHashVal,
         amt |-> GenesisBalance]]]
  /\ recvd' = Broadcast(lastHash')

\* Send: the sender's account must have enough balance to cover the amount.
CreateSendBlock(n, k, amt) ==
  /\ lastHash # NoHash
  /\ lastHash' = CalculateHash([pubKey |-> k, prevHash |-> lastHash, amt |-> amt])
  /\ ChainBalance(n, lastHash) >= amt
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
        [hash |-> lastHash', pubKey |-> k, prevHash |-> lastHash, amt |-> amt]]]
  /\ recvd' = Broadcast(lastHash')

\* Open: the first block in a chain must reference a send block that no one has
\* yet claimed, and the open block itself carries no amount.
CreateOpenBlock(n, k, funder) ==
  /\ lastHash # NoHash
  /\ ledger[n][funder].pubKey # k
  /\ lastHash' = CalculateHash([pubKey |-> k, prevHash |-> funder, amt |-> 0])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
        [hash |-> lastHash', pubKey |-> k, prevHash |-> funder, amt |-> 0]]]
  /\ recvd' = Broadcast(lastHash')

\* Receive: the receiving block references its own previous block and the funder.
CreateReceiveBlock(n, k, funder) ==
  /\ lastHash # NoHash
  /\ ledger[n][funder].pubKey = k
  /\ ChainBalance(n, funder) <= GenesisBalance - ledger[n][funder].amt
  /\ lastHash' = CalculateHash([pubKey |-> k, prevHash |-> funder, amt |-> 0])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
        [hash |-> lastHash', pubKey |-> k, prevHash |-> funder, amt |-> 0]]]
  /\ recvd' = Broadcast(lastHash')

\* Change of voting representative: always allowed for any account.
CreateChangeBlock(n, k) ==
  /\ lastHash # NoHash
  /\ lastHash' = CalculateHash([pubKey |-> k, prevHash |-> lastHash, amt |-> 0])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
        [hash |-> lastHash', pubKey |-> k, prevHash |-> lastHash, amt |-> 0]]]
  /\ recvd' = Broadcast(lastHash')

\* Receiving nodes validate every block that arrives in their received set.
ValidateBlock(n, h) ==
  /\ h \in recvd[n]
  /\ ledger[n][h].hash = h
  /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![h] = ledger[n][h]]]
  /\ recvd' = [recvd EXCEPT ![n] = recvd[n] \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node, k \in PrivateKey : CreateGenesisBlock(n, k)
  \/ \E n \in Node, k \in PrivateKey, amt \in 1..GenesisBalance : CreateSendBlock(n, k, amt)
  \/ \E n \in Node, k \in PrivateKey, funder \in Blocks : CreateOpenBlock(n, k, funder)
  \/ \E n \in Node, k \in PrivateKey, funder \in Blocks : CreateReceiveBlock(n, k, funder)
  \/ \E n \in Node, k \in PrivateKey : CreateChangeBlock(n, k)
  \/ \E n \in Node, h \in Blocks : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

====