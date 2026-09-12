---- MODULE W4Od6m8p1t5 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ctrls, MaxVal

VARIABLES dispatch, locks, snapshots, in_update, admin_override

TypeOK ==
  /\ dispatch \in [0..MaxVal]
  /\ locks \in [0..MaxVal] -> BOOLEAN
  /\ snapshots \in [0..MaxVal] -> [0..MaxVal]
  /\ in_update \subseteq Ctrls
  /\ admin_override \in BOOLEAN

Init ==
  /\ dispatch = 0
  /\ locks = [c \in Ctrls |-> FALSE]
  /\ snapshots = [c \in Ctrls |-> 0]
  /\ in_update = {}
  /\ admin_override = FALSE

Next ==
  /\ admin_override' = admin_override
  /\ \A c \in Ctrls : (locks[c] \wedge in_update' = in_update \cup {c} \Rightarrow
                      snapshots' = [snap \in snapshots | snap \in {snap : snap \neq snapshots[c]} \cup {snapshots[c] + 1}]
                      \wedge dispatch' = dispatch + snapshots[c])
  /\ \A c \in Ctrls : (locks[c] \wedge in_update' = in_update \cup {c} \Rightarrow
                      locks' = [l \in locks | l \in {locks[c]} \cup {FALSE : l \neq locks[c]}])
  /\ \A c \in Ctrls : (locks[c] \wedge in_update' = in_update \cup {c} \Rightarrow
                      snapshots' = [snap \in snapshots | snap \in {snap : snap \neq snapshots[c]} \cup {snapshots[c] + 1}])
  /\ \A c \in Ctrls : (locks[c] \wedge in_update' = in_update \cup {c} \Rightarrow
                      in_update' = in_update)
  /\ \A c \in Ctrls : (locks[c] \wedge in_update' = in_update \cup {c} \Rightarrow
                      admin_override' = FALSE)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow locks' = [l \in locks | l \in {locks[c]} \cup {FALSE : l \neq locks[c]}])
  /\ \A c \in Ctrls : (locks[c] \Rightarrow in_update' = in_update)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow admin_override' = FALSE)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow snapshots' = [snap \in snapshots | snap \in {snap : snap \neq snapshots[c]} \cup {snapshots[c]}])
  /\ \A c \in Ctrls : (locks[c] \Rightarrow dispatch' = dispatch)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow in_update' = in_update)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow admin_override' = FALSE)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow snapshots' = [snap \in snapshots | snap \in {snap : snap \neq snapshots[c]} \cup {snapshots[c]}])
  /\ \A c \in Ctrls : (locks[c] \Rightarrow dispatch' = dispatch)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow in_update' = in_update)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow admin_override' = FALSE)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow snapshots' = [snap \in snapshots | snap \in {snap : snap \neq snapshots[c]} \cup {snapshots[c]}])
  /\ \A c \in Ctrls : (locks[c] \Rightarrow dispatch' = dispatch)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow in_update' = in_update)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow admin_override' = FALSE)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow snapshots' = [snap \in snapshots | snap \in {snap : snap \neq snapshots[c]} \cup {snapshots[c]}])
  /\ \A c \in Ctrls : (locks[c] \Rightarrow dispatch' = dispatch)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow in_update' = in_update)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow admin_override' = FALSE)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow snapshots' = [snap \in snapshots | snap \in {snap : snap \neq snapshots[c]} \cup {snapshots[c]}])
  /\ \A c \in Ctrls : (locks[c] \Rightarrow dispatch' = dispatch)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow in_update' = in_update)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow admin_override' = FALSE)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow snapshots' = [snap \in snapshots | snap \in {snap : snap \neq snapshots[c]} \cup {snapshots[c]}])
  /\ \A c \in Ctrls : (locks[c] \Rightarrow dispatch' = dispatch)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow in_update' = in_update)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow admin_override' = FALSE)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow snapshots' = [snap \in snapshots | snap \in {snap : snap \neq snapshots[c]} \cup {snapshots[c]}])
  /\ \A c \in Ctrls : (locks[c] \Rightarrow dispatch' = dispatch)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow in_update' = in_update)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow admin_override' = FALSE)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow snapshots' = [snap \in snapshots | snap \in {snap : snap \neq snapshots[c]} \cup {snapshots[c]}])
  /\ \A c \in Ctrls : (locks[c] \Rightarrow dispatch' = dispatch)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow in_update' = in_update)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow admin_override' = FALSE)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow snapshots' = [snap \in snapshots | snap \in {snap : snap \neq snapshots[c]} \cup {snapshots[c]}])
  /\ \A c \in Ctrls : (locks[c] \Rightarrow dispatch' = dispatch)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow in_update' = in_update)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow admin_override' = FALSE)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow snapshots' = [snap \in snapshots | snap \in {snap : snap \neq snapshots[c]} \cup {snapshots[c]}])
  /\ \A c \in Ctrls : (locks[c] \Rightarrow dispatch' = dispatch)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow in_update' = in_update)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow admin_override' = FALSE)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow snapshots' = [snap \in snapshots | snap \in {snap : snap \neq snapshots[c]} \cup {snapshots[c]}])
  /\ \A c \in Ctrls : (locks[c] \Rightarrow dispatch' = dispatch)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow in_update' = in_update)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow admin_override' = FALSE)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow snapshots' = [snap \in snapshots | snap \in {snap : snap \neq snapshots[c]} \cup {snapshots[c]}])
  /\ \A c \in Ctrls : (locks[c] \Rightarrow dispatch' = dispatch)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow in_update' = in_update)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow admin_override' = FALSE)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow snapshots' = [snap \in snapshots | snap \in {snap : snap \neq snapshots[c]} \cup {snapshots[c]}])
  /\ \A c \in Ctrls : (locks[c] \Rightarrow dispatch' = dispatch)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow in_update' = in_update)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow admin_override' = FALSE)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow snapshots' = [snap \in snapshots | snap \in {snap : snap \neq snapshots[c]} \cup {snapshots[c]}])
  /\ \A c \in Ctrls : (locks[c] \Rightarrow dispatch' = dispatch)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow in_update' = in_update)
  /\ \A c \in Ctrls : (locks[c] \Rightarrow admin_override' = FALSE)
  /\ \A c \in Ctrls : (locks[c]