---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME GenesisBalance \in Nat

RECURSIVE ChainBalance(_, _)
ChainBalance(hash, acct) ==
  IF hash = NoHashVal THEN 0
  ELSE IF acct(hash) = acct THEN ChainBalance(Ledger[NoHash])[acct]
  ELSE ChainBalance(Ledger[NoHash])[acct]

RECURSIVE ChainExists(_, _)
ChainExists(hash, acct) ==
  IF hash = NoHashVal THEN FALSE
  ELSE IF acct(hash) = acct THEN TRUE
  ELSE ChainExists(Ledger[NoHash], acct)

SignedBlocks == [acct : PublicKey, ptype : {"genesis", "send", "open", "receive", "change"},
                 prev : Hash, src : PublicKey, dst : PublicKey, amount : Nat,
                 sig : PrivateKey]

VARIABLES lastHash, ledger, recvSet

vars == <<lastHash, ledger, recvSet>>

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Hash -> [Node -> SignedBlocks \cup {NoBlockVal}]]
  /\ recvSet \in [Node -> SUBSET Hash]

LedgerConsistent ==
  /\ \A h \in Hash : \A n \in Node : ledger[h][n] \in SignedBlocks \cup {NoBlockVal}
  /\ \A n \in Node : \A h \in Hash : recvSet[n] \subseteq Hash

ValidSignature(n, h) ==
  \/ (\E k \in PrivateKey : ledger[h][n].sig = k /\ PublicKey[k] = ledger[h][n].acct)
  \/ ledger[h][n].ptype = "genesis"

SafetyInvariant ==
  /\ LedgerConsistent
  /\ \A h \in Hash, n \in Node : ledger[h][n] # NoBlockVal => ValidSignature(n, h)

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [h \in Hash |-> [n \in Node |-> NoBlockVal]]
  /\ recvSet = [n \in Node |-> {}]

CreateGenesis(n) ==
  /\ lastHash = NoHashVal
  /\ lastHash' = CalculateHash(<<n, "genesis", NoHashVal, NoHashVal, GenesisBalance>>, NoHashVal)
  /\ \E k \in PrivateKey :
      /\ ledger' = [ledger EXCEPT ![lastHash] = [n \in Node |-> [acct |-> PublicKey[k],
                                                                ptype |-> "genesis", prev |-> NoHashVal,
                                                                src |-> NoHashVal, dst |-> NoHashVal,
                                                                amount |-> GenesisBalance, sig |-> k]]]
  /\ recvSet' = [n \in Node |-> {}]

CreateSendBlock(n, k) ==
  /\ lastHash # NoHashVal
  /\ ChainBalance(lastHash, PublicKey[k]) > 0
  /\ lastHash' = CalculateHash(<<n, "send", lastHash, PublicKey[k], NoHashVal, 1>>, lastHash)
  /\ \E dst \in PublicKey :
      ledger' = [ledger EXCEPT ![lastHash] = [n \in Node |-> [acct |-> PublicKey[k],
                                                              ptype |-> "send", prev |-> lastHash,
                                                              src |-> PublicKey[k], dst |-> dst,
                                                              amount |-> 1, sig |-> k]]]
  /\ recvSet' = [m \in Node |-> recvSet[m] \cup {lastHash}]

CreateOpenBlock(n, k) ==
  /\ lastHash # NoHashVal
  /\ \E srcHash \in Hash :
      /\ ledger[srcHash][n].ptype = "send"
      /\ ledger[srcHash][n].dst = PublicKey[k]
      /\ ledger[srcHash][n].acct # PublicKey[k]
      /\ ChainExists(srcHash, PublicKey[k]) = FALSE
      /\ lastHash' = CalculateHash(<<n, "open", srcHash, NoHashVal, NoHashVal, 1>>, lastHash)
      /\ ledger' = [ledger EXCEPT ![lastHash] = [n \in Node |-> [acct |-> PublicKey[k],
                                                                ptype |-> "open", prev |-> srcHash,
                                                                src |-> NoHashVal, dst |-> NoHashVal,
                                                                amount |-> 1, sig |-> k]]]
  /\ recvSet' = [m \in Node |-> recvSet[m] \cup {lastHash}]

CreateReceiveBlock(n, k) ==
  /\ lastHash # NoHashVal
  /\ \E srcHash \in Hash :
      /\ ledger[srcHash][n].ptype = "send"
      /\ ledger[srcHash][n].dst = PublicKey[k]
      /\ ChainExists(srcHash, PublicKey[k]) = TRUE
      /\ lastHash' = CalculateHash(<<n, "receive", srcHash, NoHashVal, NoHashVal, 1>>, lastHash)
      /\ ledger' = [ledger EXCEPT ![lastHash] = [n \in Node |-> [acct |-> PublicKey[k],
                                                                ptype |-> "receive", prev |-> srcHash,
                                                                src |-> NoHashVal, dst |-> NoHashVal,
                                                                amount |-> 1, sig |-> k]]]
  /\ recvSet' = [m \in Node |-> recvSet[m] \cup {lastHash}]

CreateChangeRepBlock(n, k) ==
  /\ lastHash # NoHashVal
  /\ ChainExists(lastHash, PublicKey[k])
  /\ lastHash' = CalculateHash(<<n, "change", lastHash, NoHashVal, NoHashVal, 0>>, lastHash)
  /\ ledger' = [ledger EXCEPT ![lastHash] = [n \in Node |-> [acct |-> PublicKey[k],
                                                            ptype |-> "change", prev |-> lastHash,
                                                            src |-> NoHashVal, dst |-> NoHashVal,
                                                            amount |-> 0, sig |-> k]]]
  /\ recvSet' = [m \in Node |-> recvSet[m] \cup {lastHash}]

ValidateBlock(n, h) ==
  /\ h \in recvSet[n]
  /\ ledger[h][n] = NoBlockVal
  /\ \E k \in PrivateKey :
        /\ ledger' = [ledger EXCEPT ![h][n] = [acct |-> PublicKey[k],
                                                ptype |-> ledger[h][n].ptype,
                                                prev |-> ledger[h][n].prev,
                                                src |-> ledger[h][n].src,
                                                dst |-> ledger[h][n].dst,
                                                amount |-> ledger[h][n].amount,
                                                sig |-> k]]
  /\ recvSet' = [recvSet EXCEPT ![n] = {h \in recvSet[n] : h # h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node : CreateGenesis(n)
  \/ \E n \in Node, k \in PrivateKey : CreateSendBlock(n, k)
  \/ \E n \in Node, k \in PrivateKey : CreateOpenBlock(n, k)
  \/ \E n \in Node, k \in PrivateKey : CreateReceiveBlock(n, k)
  \/ \E n \in Node, k \in PrivateKey : CreateChangeRepBlock(n, k)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

NoHash == NoHashVal
NoBlock == NoBlockVal

====