import Data.List as List
open List using (_∷_; []; List)
open import Data.Nat using (ℕ)
open import Data.Bool using (true; false; T) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Data.String.Properties using (<-strictTotalOrder-≈)
open import Data.Tree.AVL.Map (<-strictTotalOrder-≈) using (Map)
import Data.Tree.AVL.Sets (<-strictTotalOrder-≈) as Sets
open Sets using (⟨Set⟩)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using () renaming (_⊎_ to _∪_; inj₁ to ∪₁; inj₂ to ∪₂)
open import Level as AgdaLevel using (_⊔_; 0ℓ) renaming (Level to Setℓ; suc to sucℓ)
open import Effect.Applicative using (RawAlternative)
open import Data.List.Instances using (listAlternative)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_; refl; prep; swap; trans)
open import Data.List.Membership.Propositional -- using (_∈_)
-- open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥)


open RawAlternative ⦃...⦄

-- Cute alias List A = [ A ]
[_] = List

infixl 6 _+ₑ_
data E {ℓғ ℓɢ : Setℓ}
        {A : Set ℓғ}
        {F : Set ℓғ → Set ℓɢ}
        ⦃ 𝒜 : RawAlternative F ⦄
        : F A → Set (sucℓ ℓғ ⊔ ℓɢ)
        where
  var  : (a : A) → E (pure a)
  nat  : ℕ → E empty
  _+ₑ_ : {aₗ aᵣ : F A} → E aₗ → E aᵣ → E (aₗ <|> aᵣ)

-- data EqivExpr List 

exp₁ : E ("a" ∷ "b" ∷ "c" ∷ [])
exp₁ = nat 1 +ₑ var "a" +ₑ var "b" +ₑ var "c"

data Level : Set where
  low  : Level
  high : Level

{-
infix  3 _⟨_⟩:=_ _:=_
infixl 2 _⨟_
data C {ℓ} (Var : Set ℓ) : Set ℓ where
  skip  : C Var
  _⟨_⟩:=_  : String → Level → Expr Var → C Var
  _:=_  : String → Expr Var → C Var
  _⨟_   : C Var → C Var → C Var
  while : Expr Var → C Var → C Var
  if    : Expr Var → C Var → C Var → C Var
-}


-- Var = Map (Expr × Level)



data BasedType : Set where
  nat : BasedType

Type = BasedType × Level

{-
ex₁ : C String
ex₁ =
  "var1" ⟨ low ⟩:= zero ⨟
  "var2" ⟨ high ⟩:= add (var "var1") (succ zero) ⨟
  "var3" ⟨ low ⟩:= add (var "var1") (var "var2") ⨟
  skip
-}

valueUp : Level → Level → Level
valueUp low  y = y
valueUp high _ = high

{-
data _⊢_ϵ_ (v : Var) : Expr → Type → Set where
  zeroT : v ⊢ zero ϵ (nat , low)
  succT : {e : Expr} → {t : Type} → v ⊢ e ϵ t → v ⊢ succ e ϵ t
  addT  : {e₁ e₂ : Expr} → {t : BasedType} → {l₁ l₂ : Level} →
           v ⊢ e₁ ϵ (t , l₁) → v ⊢ e₂ ϵ (t , l₂) →
           --------------------------------
           v ⊢ add e₁ e₂ ϵ (t , valueUp l₁ l₂)
  varT  : {name : String} {v₁} → v ⊢ var name ϵ {!!}


data _∈_ : C → Type → Set where
  ifₕ : {!!}
  ifₗ : {e : Expr} → {c₁ c₂ : C} → {t : BasedType} → {!!} → c₁ ∈ (t , low) → c₂ ∈ (t , low) → {!!}
-}
