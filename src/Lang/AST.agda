-- Simple AST so we can represent the examples in the paper
module Lang.AST where
open import Data.Nat using (ℕ)

data Var : Set where
  l : Var
  h : Var

data Exp : Set where
  var   : Var → Exp
  litℕ  : ℕ → Exp
  _=ₑ_  : Exp → Exp → Exp
  _mod_ : Exp → Exp → Exp

infix  5 _:=_
infix  5 if_then_else_
infix  5 while_exec_
infixr 3 _⨟_
data Cmd : Set where
  skip          : Cmd
  _:=_          : Var → Exp → Cmd
  _⨟_           : Cmd → Cmd → Cmd
  while_exec_   : Exp → Cmd → Cmd
  if_then_else_ : Exp → Cmd → Cmd → Cmd
