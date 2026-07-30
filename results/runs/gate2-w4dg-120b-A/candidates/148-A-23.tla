---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME NoHashVal \notin Hash /\ NoBlockVal \notin Hash /\ GenesisBalance \in Nat /\ GenesisBalance > 0

VARIABLES lastHash, ledger, received, authBy

vars == <<lastHash, ledger, received, authBy>>

Bands == {"genesis", "send", "open", "receive", "change"}

RECURSIVE SumFn(_, _)
SumFn(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumFn(f, S \ {x})

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> Bands \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]
  /\ authBy \in [Hash -> PublicKey \cup {NoHashVal}]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]
  /\ authBy = [h \in Hash |-> NoHashVal]

BalanceOf(n, h) ==
  LET g[hh \in Hash] ==
        IF ledger[n][hh] = "genesis" THEN GenesisBalance
        ELSE IF ledger[n][hh] = "send" THEN BalanceOf(n, hh) - 1
        ELSE IF ledger[n][hh] = "receive" THEN BalanceOf(n, hh) + 1
        ELSE IF ledger[n][hh] = "open" THEN BalanceOf(n, hh) + 1
        ELSE IF ledger[n][hh] = "change" THEN BalanceOf(n, hh)
        ELSE 0
  IN g[h]

Validate(h, n) ==
  /\ ledger[n][h] = NoBlockVal
  /\ authBy[h] # NoHashVal
  /\ authBy[h] \notin {NoHashVal} /\ authBy[h] \in PublicKey
  /\ ledger[n][lastHash] # NoBlockVal
  /\ CASE ledger[n][h] = "genesis" -> h = NoHashVal
          ledger[n][h] = "send" -> BalanceOf(n, lastHash) >= 1
          ledger[n][h] = "receive" -> BalanceOf(n, lastHash) + 1 <= GenesisBalance
          ledger[n][h] = "open" -> TRUE
          ledger[n][h] = "change" -> TRUE
          OTHER -> FALSE

CreateGenesis(nk) ==
  /\ lastHash = NoHashVal
  /\ lastHash' = CalculateHash("genesis", NoHashVal)
  /\ authBy' = [authBy EXCEPT ![lastHash'] = nk]
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = "genesis"]]
  /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

CreateSend(nk) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHash("send", lastHash)
  /\ authBy' = [authBy EXCEPT ![lastHash'] = nk]
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = "send"]]
  /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

CreateOpen(nk) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHash("open", lastHash)
  /\ authBy' = [authBy EXCEPT ![lastHash'] = nk]
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = "open"]]
  /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

CreateReceive(nk) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHash("receive", lastHash)
  /\ authBy' = [authBy EXCEPT ![lastHash'] = nk]
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = "receive"]]
  /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

CreateChange(nk) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHash("change", lastHash)
  /\ authBy' = [authBy EXCEPT ![lastHash'] = nk]
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = "change"]]
  /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

ProcessBlock(n) ==
  /\ \E h \in received[n] :
       /\ Validate(h, n)
       /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![h] = ledger[n][h]]]
       /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED <<lastHash, authBy>>

Next ==
  \/ \E nk \in PrivateKey : CreateGenesis(nk) \/ CreateSend(nk) \/ CreateOpen(nk) \/ CreateReceive(nk) \/ CreateChange(nk)
  \/ \E n \in Node : ProcessBlock(n)

Spec == Init /\ [][Next]_vars

SignatureValid(h, n) == ledger[n][h] # NoBlockVal => authBy[h] \in PublicKey

SafetyInvariant == \A n \in Node : \A h \in Hash : SignatureValid(h, n)

====