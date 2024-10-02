open import Agda.Builtin.Nat renaming (suc to succ; Nat to ℕ)
open import Data.String
open import Data.String.Properties
open import Data.Tree.AVL.Map (<-strictTotalOrder-≈)
open import Data.Maybe

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data Level : Set where
  low  : Level
  high : Level

mutual
    Var = Map (Expr ℕ × Level)

    data Expr : Set → Set where
        nInt  : (n : ℕ) → Expr ℕ
        add   : Expr ℕ → Expr ℕ → Expr ℕ
        var   : Var → Expr ℕ
