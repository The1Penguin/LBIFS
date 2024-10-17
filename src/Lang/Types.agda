module Lang.Types where
open import Data.List using (_∷_; []; List; _++_)
open import Data.List.Membership.Propositional using (_∉_)
open import Data.List.Relation.Unary.Any using (tail)
open import Data.Sum using () renaming (_⊎_ to _∪_; inj₁ to ∪₁; inj₂ to ∪₂)
open import Lang.AST
open import Lang.TC

infix 2 _⊢_

data Lvl : Set where
  high : Lvl
  low  : Lvl

data SecContext : Set where
  [high] : SecContext
  [low]  : SecContext

variable
  exp : Exp
  C C₁ C₂ : Cmd
  pc : Lvl
  [pc] : SecContext



Vars : Exp → List Var
Vars l = l ∷ []
Vars h = h ∷ []
Vars (litℕ x) = []
Vars (e =ₑ e₁) = Vars e ++ Vars e₁
Vars (e mod e₁) = Vars e ++ Vars e₁

data ⊢_⦂_ (exp : Exp) : Lvl → Set where
  E1 : ⊢ exp ⦂ high
  E2 : h ∉ Vars(exp)
     → -------------
        ⊢ exp ⦂ low

data _⊢_ : SecContext → Cmd → Set where
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
       [pc] ⊢ while exp exec C

  C6 : ⊢ exp ⦂ pc → [pc] ⊢ C₁ → [pc] ⊢ C₂
     → ----------------------------------
         [pc] ⊢ if exp then C₁ else C₂

  C7 : [high] ⊢ C
     → ----------
        [low] ⊢ C



fromCtx : SecContext → Lvl
fromCtx [high] = high
fromCtx [low]  = low

noHigh : (vs : List Var) → TC (h ∉ vs)
noHigh [] = pure (λ ())
noHigh (h ∷ vs) = fail "Cannot type low in a high context"
noHigh (l ∷ vs) = do
  h∉vs ← noHigh vs
  pure λ h∈l∷vs → h∉vs (tail (λ ()) h∈l∷vs)

typableExp : (lvl : Lvl) (exp : Exp) → TC (⊢ exp ⦂ lvl)
typableExp low  e = E2 <$> (noHigh (Vars e))
typableExp high e = pure E1


mutual
  trySubsum : ([pc] : SecContext) (cmd : Cmd) → TC ([pc] ⊢ cmd)
  trySubsum [high] C = typableCmd [high] C
  trySubsum [low]  C with typableCmd [low] C | typableCmd [high] C
  ... | ∪₂ y | _        = pure y
  ... | ∪₁ _ | fallback = ⦇ C7 fallback ⦈

  typableCmd : ([pc] : SecContext) (cmd : Cmd) → TC ([pc] ⊢ cmd)
  typableCmd [pc]   skip     = pure C1
  typableCmd [pc]   (h := _) = pure C2
  typableCmd [high] (l := e) = fail "Cannot modify low variable in a high context"
  typableCmd [low]  (l := e) = C3 <$> typableExp low e
  typableCmd [pc]   (C ⨟ C₁) = ⦇ C4 (trySubsum [pc] C) (trySubsum [pc] C₁) ⦈
  typableCmd [pc]   (while e exec C)
    = ⦇ C5 (typableExp (fromCtx [pc]) e) (trySubsum [pc] C) ⦈
  typableCmd [pc]   (if e then C else C₁)
    = ⦇ C6 (typableExp (fromCtx [pc]) e) (trySubsum [pc] C) (trySubsum [pc] C₁) ⦈
