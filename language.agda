open import Data.Nat
open import Data.String
open import Data.String.Properties
open import Data.Tree.AVL.Map (<-strictTotalOrder-≈)
open import Data.Maybe

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data _∪_ (A B : Set) : Set where
  ∪₁ : A → A ∪ B
  ∪₂ : B → A ∪ B

data Level : Set where
  low  : Level
  high : Level

mutual
    Var = Map (Expr × Level)

    data Expr : Set where
        zero  : Expr
        succ  : Expr → Expr
        add   : Expr → Expr → Expr
        var   : String → Expr

data BasedType : Set where
  nat : BasedType

Type = BasedType × Level

data C : Set where
  skip  : C
  _:=_  : String → Level → Expr → C
  _⨟_   : C → C → C
  while : Expr → C → C
  if    : Expr → C → C → C

valueUp : Level → Level → Level
valueUp low  y = y
valueUp high _ = high

data _⊢_ϵ_ (v : Var) : Expr → Type → Set where
  zeroT : v ⊢ zero ϵ (nat , low)
  succT : {e : Expr} → {t : Type} → v ⊢ e ϵ t → v ⊢ succ e ϵ t
  addT  : {e₁ e₂ : Expr} → {t : BasedType} → {l₁ l₂ : Level} →
           v ⊢ e₁ ϵ (t , l₁) → v ⊢ e₂ ϵ (t , l₂) →
           --------------------------------
           v ⊢ add e₁ e₂ ϵ (t , valueUp l₁ l₂)
  varT  : {name : String} → v ⊢ var name ϵ {!!}


data _∈_ : C → Type → Set where
  ifₕ : {!!}
  ifₗ : {e : Expr} → {c₁ c₂ : C} → {t : BasedType} → {!!} → c₁ ∈ (t , low) → c₂ ∈ (t , low) → {!!}
