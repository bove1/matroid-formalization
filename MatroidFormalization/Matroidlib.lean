import Aesop
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option tactic.hygienic false
set_option linter.unusedVariables false

open Lean
open Lean.Parser
open Lean.Parser.Term
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

#check Finset
