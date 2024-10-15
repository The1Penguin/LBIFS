module lang where

data Exp : Set where
  var  : Identifier → Set -- x
  loc  : Address → Set    -- l
  lit  : ℕ → Set          -- n
  _+_  : Exp → Exp → Set  -- e+e′
  _-_  : Exp → Exp → Set  -- e-e′
  _＝_ : Exp → Exp → Set  -- e=e′
  _<_  : Exp → Exp → Set  -- e<e′

data Cmd : Set where
  _:=_           : Exp → Exp → Set       -- e:=e′
  _⨟_            : Cmd → Cmd → Set       -- c;c′
  if_then_else_  : Exp → Cmd → Cmd → Set -- if e then c else c′
  while_exec_    : Exp → Cmd → Set       -- while e do c
  letvar_:=_for_ : Exp → Exp → Cmd → Set -- letvar x := e in c TODO: restrict x to an identifier

data Judgment : Set where
  γ ⊢ p ⦂ τ : Judgment

data SecContext : Set where
  [high] : SecContext
  [low]  : SecContext

variable
  [pc] : SecContext

data exp : Set where
  E1 : ⊢ exp ⦂ high
  E2 : h ∉ Vars(exp)
     → -------------
        ⊢ exp ⦂ low

data Test : Set where
  C1 : [pc] ⊢ skip
  C2 : [pc] ⊢ h := exp

  C3 :   ⊢ exp ⦂ low
     → ----------------
       [low] ⊢ l := exp

  C4 : [pc] ⊢ C₁ → [pc] ⊢ C₂
     → ---------------------
          [pc] ⊢ C₁ ⨟ C₂

  C5 : ⊢ exp ⦂ pc → [pc] ⊢ C
     → ---------------------
       [pc] ⊢ while exp do C

  C6 : ⊢ exp ⦂ pc → [pc] ⊢ C₁ → [pc] ⊢ C₂
     → ----------------------------------
         [pc] ⊢ if exp then C₁ else C₂

  C7 : [high] ⊢ C
     → ----------
        [low] ⊢ C
