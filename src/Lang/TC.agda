-- Renamied Either Monad to enable failing operations
module Lang.TC where
open import Data.String using (String)
open import Data.Sum using (inj₁)
import Data.Sum.Effectful.Left as LeftSum
open import Effect.Monad using (RawMonad)
open import Level using (0ℓ)

open RawMonad ⦃...⦄ public

open LeftSum String 0ℓ using () renaming (Sumₗ to TC; monad to leftSumMonad) public
instance
  eitherMonad : RawMonad TC
  eitherMonad = leftSumMonad

fail : ∀ {A} String → TC A
fail = inj₁
