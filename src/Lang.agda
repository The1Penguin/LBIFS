module Lang where
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Lang.AST
open import Lang.Semantics
open import Lang.TC
open import Lang.Types
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

codeEx₁ : Cmd
codeEx₁ =
  h := var h mod litℕ 2 ⨟
  l := litℕ 0 ⨟
  if var h =ₑ litℕ 1 then l := litℕ 1
                     else skip
code⊥ : Cmd
code⊥ =
  while litℕ 0 =ₑ litℕ 0 exec skip

codeEx₂ : Cmd
codeEx₂ = skip

data Safe {l₀ h₀ h₁} (C : Cmd) : Set where
  safe : ⟦ C ⟧ (h₀ , l₀) ≈ₗ ⟦ C ⟧ (h₁ , l₀) → Safe C

safet : ∀ {C} {l₀ h₀ h₁} → {h₀ ≢ h₁} → Result × Result
safet {C} {l₀} {h₀} {h₁} = ( ⟦ C ⟧ (h₀ , l₀) , ⟦ C ⟧ (h₁ , l₀) )

unsafe : Safe codeEx₁
unsafe = safe {0} {0} {0} {codeEx₁} refl

issafe : Safe codeEx₂
issafe = safe refl

issafe? : ∀ {l₀ h₀ h₁} → Safe (l := var h)
issafe? {l₀} {h₀} {h₁} = safe {l₀} {h₀} {h₁} {l := var h} ?
issafe! = safet {l := var h} {0} {1}


typeₑ0 : ⊢ litℕ 0 ⦂ low
typeₑ0 = E2 (λ ())
typeₑ1 : ⊢ var h ⦂ low
typeₑ1 = ? -- Not typeable

typedₑ1 : TC (⊢ var h ⦂ low)
typedₑ1 = typableExp low (var h)


cmd : Cmd
cmd = codeEx₁ -- l := var h

typed : TC ([low] ⊢ cmd)
typed = typableCmd [low] cmd

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
