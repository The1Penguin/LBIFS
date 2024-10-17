module NumberOverload where
open import Data.Nat using (ℕ)
open import Lang.AST using (litℕ; Exp)

record Number {a} (A : Set a) : Set a where
  field fromNat : ℕ → A

open Number {{...}} public
{-# BUILTIN FROMNAT fromNat #-}

instance
  basicNats : Number ℕ
  basicNats .fromNat n = n

  astNats : Number Exp
  astNats .fromNat = litℕ
