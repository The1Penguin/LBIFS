------------------------------------------------------------------------
-- AST with type level restriction on free variables
--
-- Pros: Composable statements, e.g. we can design a function that
--       requires a block with a single free variable called "freevar"
-- Cons: Inflexible, very long error messages,
--       and possibly tougher to add additional proofs
------------------------------------------------------------------------
module bubbleup where
open import Data.Nat using (ℕ)
open import Data.String using (String)
import Data.List as List
open List using (_∷_; []; List)
open import Level as AgdaLevel using (_⊔_)

open import Relation.Binary.Bundles using (StrictTotalOrder)
module Definintions {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂) where
  open import Data.Tree.AVL.Sets strictTotalOrder as Sets using (⟨Set⟩)
  open import Data.Tree.AVL.Map strictTotalOrder as Map using (Map)
  open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)

  data Level : Set where
    low  : Level
    high : Level

  variable
    d f f₁ f₂ : ⟨Set⟩
    Γ : Map Level
  ℓ = (a ⊔ ℓ₂)

  infixl 6 _+ₑ_
  --   Expr : Frees → Set
  data Expr : ⟨Set⟩ → Set ℓ where
    var  : (var : Key) → Expr (Sets.singleton var)
    nat  : ℕ → Expr Sets.empty
    _+ₑ_ : Expr f₁ → Expr f₂ → Expr (Sets.union f₁ f₂)

  infix  4 _⟨_⟩:=_ _:=_
  infixr 2 _⨟_
  infix  3 _⨟
  mutual
    --   Block : Frees → Set
    data Block : ⟨Set⟩ → Set ℓ where
      _⨟_ : C d f₁ → Block f₂ → Block (Sets.union f₁ (Sets.foldr Sets.delete f₂ d))
      _⨟  : C d f → Block f

    --   C : Decls → Frees → Set
    data C : ⟨Set⟩ → ⟨Set⟩ → Set ℓ where
      skip          : C Sets.empty Sets.empty
      _⟨_⟩:=_       : (var : Key) → Level → Expr f → C (Sets.singleton var) f
      _:=_          : (var : Key) → Expr f → C Sets.empty (Sets.insert var f)
      while_｛_｝   : Expr f₁ → Block f₂ → C Sets.empty (Sets.union f₁ f₂)
      if_｛_｝｛_｝ : Expr f → Block f₁ → Block f₂ → C Sets.empty (Sets.union f (Sets.union f₁ f₂))

open import Data.String.Properties using (<-strictTotalOrder-≈)
open Definintions (<-strictTotalOrder-≈)
import Data.Tree.AVL.Sets (<-strictTotalOrder-≈) as Sets
open Sets using (⟨Set⟩)

exp₁ : Expr (Sets.fromList ("a" ∷ "b" ∷ "c" ∷ []))
exp₁ = nat 1 +ₑ var "a" +ₑ var "b" +ₑ var "c"

ex₁ : Block (Sets.fromList ("var?" ∷ []))
ex₁ =
  "var1" ⟨ low ⟩:= nat 0 ⨟
  while var "var1" ｛ skip ⨟ ｝ ⨟
  if nat 0 ｛
    skip ⨟
  ｝｛
    "var4" ⟨ high ⟩:= var "var1" +ₑ nat 1 ⨟
  ｝ ⨟
  "var2" ⟨ high ⟩:= var "var?" +ₑ nat 1 ⨟
  "var3" ⟨ low ⟩:= var "var1" +ₑ var "var2" ⨟
  skip ⨟
