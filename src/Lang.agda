module Lang where
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Lang.AST
open import Lang.Semantics
open import Lang.TC
open import Lang.Types
open import NumberOverload
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

-- Don't evaluate semantics as this is not terminating
code⊥ : Cmd
code⊥ =
  while 0 =ₑ 0 exec skip





typed : (cmd : Cmd) → TC ([low] ⊢ cmd)
typed cmd = typableCmd [low] cmd

ex1 ex2 ex3 : Cmd
ex1 =
  h := h mod 2 ⨟
  l := 0 ⨟
  if h =ₑ 1 then l := 1
            else skip

ex2 =
  l := l mod 2 ⨟
  h := 0 ⨟
  if l =ₑ 1 then h := 1
            else skip

ex3 = if h =ₑ 0 then h := 1 else h := 2 ⨟
      l := 0










{-
data Safe {l₀ h₀ h₁} (C : Cmd) : Set where
  safe : ⟦ C ⟧ (h₀ , l₀) ≈ₗ ⟦ C ⟧ (h₁ , l₀) → Safe C

safet : ∀ {C} {l₀ h₀ h₁} → {h₀ ≢ h₁} → Result × Result
safet {C} {l₀} {h₀} {h₁} = ( ⟦ C ⟧ (h₀ , l₀) , ⟦ C ⟧ (h₁ , l₀) )

unsafe : Safe ex1
unsafe = safe {0} {0} {0} {ex1} refl

-- issafe : Safe ex2
-- issafe = safe refl

issafe? : ∀ {l₀ h₀ h₁} → Safe (l := var h)
issafe? {l₀} {h₀} {h₁} = safe {l₀} {h₀} {h₁} {l := var h} ?
issafe! = safet {l := var h} {0} {1}


variable
  l₀ l₁ h₀ h₁ lᵢ hᵢ vₗ vₕ : ℕ

-- safe : ∀ {l₀ h₀ h₁} → ⟦ C ⟧ (h₀ , l₀) ≈ₗ ⟦ C ⟧ (h₁ , l₀) → Safe C
sound : ∀ {l₀ h₀ h₁} {cmd : Cmd} → [low] ⊢ cmd → Safe {l₀} {h₀} {h₁} cmd
sound C1 = safe refl
sound C2 = safe refl
sound (C3 e) = {! safe refl !}
sound {l₀} {h₀} {h₁} (C4 t t₁) with sound {l₀} {h₀} {h₁} t | sound {l₀} {h₀} {h₁} t₁
... | s | s₁ = {! sound t !}
-- ⟦ C ; C1 ⟧ = ⟦ C ; C1 ⟧
sound (C5 e t) = {! !}
sound (C6 e t t₁) = {! !}
sound (C7 t) = {! safe refl !}
-}
{-
sound : ∀ {cmd : Cmd} → [low] ⊢ cmd → ∀ {l₀ h₀ h₁} → ⟦ C ⟧ (h₀ , l₀) ≈ₗ ⟦ C ⟧ (h₁ , l₀)
sound {C} C1 {l₀} {h₀} {h₁} = _
sound C2 = {! !}
sound (C3 x) = {! !}
sound (C4 r r₁) = _
sound (C5 x r) = {! !}
sound (C6 x r r₁) = {! !}
sound (C7 r) = {! !}
-}
