module lang where
open import Data.String using (String)
open import Data.Nat using (ℕ; _<ᵇ_; _≡ᵇ_; _%_; _≟_)
open import Data.Bool using (true; false; T) renaming (Bool to 𝔹; if_then_else_ to ifᵇ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using () renaming (_⊎_ to _∪_; inj₁ to ∪₁; inj₂ to ∪₂)
import Data.Sum.Effectful.Left as LeftSum
open import Data.Product using (_×_; _,_) renaming (proj₁ to ×₁; proj₂ to ×₂)
open import Data.List using (_∷_; []; List; _++_; any)
open import Data.List.Membership.Propositional using (_∈_; _∉_; find)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there; tail; head)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Effect.Monad using (RawMonad)
open import Level using (0ℓ)
open import Relation.Nullary using (does; _because_; yes; no)

open RawMonad ⦃...⦄

open LeftSum String 0ℓ renaming (Sumₗ to TC; monad to leftSumMonad)
instance
  eitherMonad : RawMonad TC
  eitherMonad = leftSumMonad

fail : ∀ {A} String → TC A
fail = ∪₁

data Var : Set where
  l : Var
  h : Var

-- AST
data Exp : Set where
  var   : Var → Exp
  litℕ  : ℕ → Exp
  _=ₑ_  : Exp → Exp → Exp
  _mod_ : Exp → Exp → Exp

infix  5 _:=_
infix  5 if_then_else_
infix  5 while_exec_
infixr 3 _⨟_
data Cmd : Set where
  skip          : Cmd
  _:=_          : Var → Exp → Cmd
  _⨟_           : Cmd → Cmd → Cmd
  while_exec_   : Exp → Cmd → Cmd
  if_then_else_ : Exp → Cmd → Cmd → Cmd

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

State : Set
State = ℕ × ℕ
sₕ : State → ℕ
sₕ = ×₁
sₗ : State → ℕ
sₗ = ×₂

_=ₗ_ : State → State → Set
-- ? l₀ .×₂ =ₗ l₁ .×₂ = l₀ ≡ l₁
(_ , l₀) =ₗ (_ , l₁) = l₀ ≡ l₁

_≈ₗ_ : State ∪ ⊥ → State ∪ ⊥ → Set
∪₁ (_ , l₀) ≈ₗ ∪₁ (_ , l₁) = l₀ ≡ l₁


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
⟦_⟧ : Cmd → State → State ∪ ⊥
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

data Safe (C : Cmd) : Set where
  safe : ∀ {vₗ vₕ} → ⟦ C ⟧ (vₗ , vₕ) ≈ₗ ⟦ C ⟧ (vₗ , vₕ) → Safe C

unsafe : Safe codeEx₁
unsafe = safe ?

issafe : Safe codeEx₂
issafe = safe refl


data Lvl : Set where
  high : Lvl
  low  : Lvl

data SecContext : Set where
  [high] : SecContext
  [low]  : SecContext

fromCtx : SecContext → Lvl
fromCtx [high] = high
fromCtx [low]  = low

-- Only used to know if there is a high in exp?
Vars : Exp → List Var
Vars (var x) = x ∷ []
Vars (litℕ x) = []
Vars (e =ₑ e₁) = Vars e ++ Vars e₁
Vars (e mod e₁) = Vars e ++ Vars e₁

-- Typing judgment
data ⊢_⦂_ (exp : Exp) : Lvl → Set where
  E1 : ⊢ exp ⦂ high
  E2 : h ∉ Vars(exp)
     → -------------
        ⊢ exp ⦂ low

noHigh : (vs : List Var) → TC (h ∉ vs)
noHigh [] = pure (λ ())
noHigh (h ∷ vs) = fail "Cannot type low in a high context"
noHigh (l ∷ vs) = do
  h∉vs ← noHigh vs
  pure λ h∈l∷vs → h∉vs (tail (λ ()) h∈l∷vs)

typeₑ0 : ⊢ litℕ 0 ⦂ low
typeₑ0 = E2 (λ ())
typeₑ1 : ⊢ var h ⦂ low
typeₑ1 = ? -- Not typeable

typableExp : (lvl : Lvl) (exp : Exp) → TC (⊢ exp ⦂ lvl)
typableExp low  e = E2 <$> (noHigh (Vars e))
typableExp high e = pure E1

typedₑ1 : TC (⊢ var h ⦂ low)
typedₑ1 = typableExp low (var h)


variable
  exp : Exp
  C C₁ C₂ : Cmd
  pc : Lvl
  [pc] : SecContext

infix 2 _⊢_
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

mutual
  trySubsum :  ([pc] : SecContext) (cmd : Cmd) → TC ([pc] ⊢ cmd)
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


cmd : Cmd
cmd = codeEx₁ -- l := var h

typed : TC ([low] ⊢ cmd)
typed = typableCmd [low] cmd

variable
  l₀ l₁ h₀ h₁ lᵢ hᵢ vₗ vₕ : ℕ

{-
--  safe : ∀ {vₗ vₕ} → ⟦ C ⟧ (vₗ , vₕ) ≈ₗ ⟦ C ⟧ (vₗ , vₕ) → Safe C
sound : ∀ {vₗ vₕ} {cmd : Cmd} → [low] ⊢ cmd → Safe cmd
sound {vₗ} {vₕ} C1 = safe refl
sound {vₗ} {vₕ} C2 = safe refl
sound {vₗ} {vₕ} (C3 e) = {! safe refl !}
sound {vₗ} {vₕ} (C4 t t₁) with sound {vₗ} {vₕ} t | sound {vₗ} {vₕ} t₁
... | s | s₁ = {! sound t !}
-- ⟦ C ; C1 ⟧ = ⟦ C ; C1 ⟧
sound {vₗ} {vₕ} (C5 e t) = {! !}
sound {vₗ} {vₕ} (C6 e t t₁) = {! !}
sound {vₗ} {vₕ} (C7 t) = {! safe refl !}
-}
