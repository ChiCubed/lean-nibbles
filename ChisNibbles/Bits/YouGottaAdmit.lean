import Lean.Elab.GuardMsgs

/--
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : "sentripitl" = "centripetal" := by admit
