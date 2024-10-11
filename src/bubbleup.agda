module bubbleup where
open import Data.Nat using (ℕ)
open import Data.String using (String)
import Data.List as List
open List using (_∷_; []; List)
open import Level as AgdaLevel using (_⊔_)

open import Relation.Binary.Bundles using (StrictTotalOrder)
module Definintions {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂) where
  import Data.Tree.AVL.Sets strictTotalOrder as Sets
  open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)
  open Sets using (⟨Set⟩)

  -- We want to represent the free variables.
  -- When evaluating we have a proof that the context contains all the free variables.
  -- To do that we need to have a proof that declaring a variable is symetric on both.
  infixl 6 _+ₑ_
  data Expr : ⟨Set⟩ → Set (a ⊔ ℓ₂) where
    var  : (a : Key) → Expr (Sets.singleton a)
    nat  : ℕ → Expr Sets.empty
    _+ₑ_ : {aₗ aᵣ : ⟨Set⟩} → Expr aₗ → Expr aᵣ → Expr (Sets.union aₗ aᵣ)

open import Data.String.Properties using (<-strictTotalOrder-≈)
open Definintions (<-strictTotalOrder-≈)
import Data.Tree.AVL.Sets (<-strictTotalOrder-≈) as Sets
open Sets using (⟨Set⟩)

exp₁ : Expr (Sets.fromList ("a" ∷ "b" ∷ "c" ∷ []))
exp₁ = nat 1 +ₑ var "a" +ₑ var "b" +ₑ var "c"
