module Lang.Semantics where
open import Data.Bool using () renaming (if_then_else_ to ifᵇ)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _≡ᵇ_; _%_)
open import Data.Product using (_×_; _,_) renaming (proj₁ to ×₁; proj₂ to ×₂)
open import Data.Sum using () renaming (_⊎_ to _∪_; inj₁ to ∪₁; inj₂ to ∪₂)
open import Lang.AST
open import Relation.Binary.PropositionalEquality using (_≡_)

State : Set
State = ℕ × ℕ -- high × low
sₕ : State → ℕ
sₕ = ×₁
sₗ : State → ℕ
sₗ = ×₂

Result : Set
Result = State ∪ ⊥

⟦_⟧ₑ : Exp → State → ℕ
⟦ var l ⟧ₑ s = sₗ s
⟦ var h ⟧ₑ s = sₕ s
⟦ litℕ n ⟧ₑ s = n
⟦ e =ₑ e₁ ⟧ₑ s with ⟦ e ⟧ₑ s | ⟦ e₁ ⟧ₑ s
... | n | n₁ = ifᵇ (n ≡ᵇ n₁) 1 0
⟦ e mod e₁ ⟧ₑ s with ⟦ e ⟧ₑ s | ⟦ e₁ ⟧ₑ s
... | n | ℕ.zero = ℕ.zero
... | n | ℕ.suc n₁ = n % ℕ.suc n₁

-- This is not decidable unless we pretend it's terminating
{-# TERMINATING #-}
⟦_⟧ : Cmd → State → Result
⟦ skip ⟧ s = ∪₁ s
⟦ l := e ⟧ s = ∪₁ (sₕ s , ⟦ e ⟧ₑ s)
⟦ h := e ⟧ s = ∪₁ (⟦ e ⟧ₑ s , sₗ s)
⟦ C ⨟ C₁ ⟧ s with ⟦ C ⟧ s
... | ∪₁ s₁ = ⟦ C₁ ⟧ s₁
⟦ if e then C else C₁ ⟧ s with ⟦ e ⟧ₑ s
... | ℕ.zero = ⟦ C₁ ⟧ s
... | ℕ.suc r = ⟦ C ⟧ s
⟦ while e exec C ⟧ s with ⟦ e ⟧ₑ s
... | ℕ.zero = ∪₁ s
... | ℕ.suc r = ⟦ C ⨟ while e exec C ⟧ s

_=ₗ_ : State → State → Set
-- ? l₀ .×₂ =ₗ l₁ .×₂ = l₀ ≡ l₁
(_ , l₀) =ₗ (_ , l₁) = l₀ ≡ l₁

_≈ₗ_ : Result → Result → Set
∪₁ (_ , l₀) ≈ₗ ∪₁ (_ , l₁) = l₀ ≡ l₁
