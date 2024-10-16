module lang where
open import Data.String using (String)
open import Data.Nat using (ℕ; _<ᵇ_; _≡ᵇ_)
open import Data.Bool using (true; false; T) renaming (Bool to 𝔹)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_×_; _,_)
open import Data.List using (_∷_; []; List; any)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Maybe using (Maybe)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)

Name : Set
Name = String

data Lvl : Set where
  high : Lvl
  low  : Lvl

-- AST
data RawExp : Set where
  var   : Name → RawExp
  litℕ  : ℕ → RawExp
  lit𝔹  : 𝔹 → RawExp
  _+ₑ_  : RawExp → RawExp → RawExp
  _-ₑ_  : RawExp → RawExp → RawExp
  _=ₑ_  : RawExp → RawExp → RawExp
  _<ₑ_  : RawExp → RawExp → RawExp
  _mod_ : RawExp → RawExp → RawExp

mutual
  infix  5 _⟨_⟩:=_ _:=_
  infixr 3 _⨟_
  infix  4 _⨟
  data RawBlk : Set where
    _⨟_ : RawCmd → RawBlk → RawBlk
    _⨟  : RawCmd → RawBlk

  data RawCmd : Set where
    skip          : RawCmd
    _⟨_⟩:=_       : Name → Lvl → RawExp → RawCmd
    _:=_          : Name → RawExp → RawCmd -- TODO: More generic?
    if_then_else_ : RawExp → RawBlk → RawBlk → RawCmd
    while_exec_   : RawExp → RawBlk → RawCmd

codeEx₁ : RawBlk
codeEx₁ =
  "h" ⟨ high ⟩:= litℕ 5 ⨟

  "h" := var "h" mod litℕ 2 ⨟
  "l" ⟨ low ⟩:= litℕ 0 ⨟
  if var "h" =ₑ litℕ 1 then (
    "l" := litℕ 1 ⨟
  ) else (
    skip ⨟
  ) ⨟

-- Typing
data BaseType : Set where
  Nat  : BaseType
  Bool : BaseType

Type : Set
Type = BaseType × Lvl

Context : Set
Context = List (Name × Type)





testlist : List ℕ
testlist = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []

testlist2 : List ℕ
testlist2 = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []

gt5 : ℕ → 𝔹
gt5 n = 5 <ᵇ n

testProof : (l : List ℕ) → T (any (5 <ᵇ_) l) → {e : ℕ} → T (5 <ᵇ e) → T (any (e ≡ᵇ_) l) → List ℕ
testProof l = {! ⊤ !}

t : List ℕ
t = testProof testlist tt {6} {! !} {! !}

{-
data Cmd (Γ : Context) : Type → Set where
  skip          : RawCmd
  _⟨_⟩:=_       : Name → Lvl → RawExp → RawCmd
  _:=_          : Name → RawExp → RawCmd -- TODO: More generic?
  if_then_else_ : RawExp → RawBlk → RawBlk → RawCmd
  while_exec_   : RawExp → RawBlk → RawCmd

variable t : Type
data Exp (Γ : Context) : Type → Set where
  var   : (x : Name) → (x, t) ∈ Γ → Exp Γ t
  litℕ  : ℕ → Exp Γ (
  lit𝔹  : 𝔹 → RawExp
  _+ₑ_  : RawExp → RawExp → RawExp
  _-ₑ_  : RawExp → RawExp → RawExp
  _=ₑ_  : RawExp → RawExp → RawExp
  _<ₑ_  : RawExp → RawExp → RawExp
  _mod_ : RawExp → RawExp → RawExp

  litℕ : (n : Nat) → Term Γ nat
  suc : Term Γ (nat => nat)
  app : (s : Term Γ (a => b)) (t : Term Γ a) → Term Γ b
  lam : (x : Name) (t : Term ((x , a) ∷ Γ) b) → Term Γ (a => b)
  var : (x : Name) → (x , a) ∈ Γ → Term Γ a
  natrec : Term Γ (a => (nat => a => a) => nat => a)


Result : Set
Result = Maybe

inferExp : (Γ : Context) (e : RawExp) → Result (WellTyped Γ e)
inferExp = ?
-}

{-
data Judgment : Set where
  γ ⊢ p ⦂ τ : Judgment

-}

data SecContext : Set where
  [high] : SecContext
  [low]  : SecContext

-- Only used to know if there is a high in exp?
Vars : RawExp → List Lvl
Vars = ?

h = high
l = low

data ⊢_⦂_ (exp : RawExp) : Lvl → Set where
  E1 : ⊢ exp ⦂ high
  E2 : h ∉ Vars(exp)
     → -------------
        ⊢ exp ⦂ low



variable
  exp : RawExp
  C C₁ C₂ : RawCmd
  pc : Lvl

infix 2 _⊢_
data _⊢_ ([pc] : SecContext) : RawCmd → Set where
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
