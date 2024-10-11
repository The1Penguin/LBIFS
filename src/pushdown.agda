module pushdown where
open import Data.Nat using (ℕ)
open import Data.String using (String)
import Data.List as List
open List using (_∷_; []; List)
open import Level as AgdaLevel using (_⊔_)

open import Relation.Binary.Bundles using (StrictTotalOrder)
module Definintions {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂) where
  open import Data.Tree.AVL.Sets strictTotalOrder using (⟨Set⟩)
  open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)
  open import Data.Tree.AVL.Sets.Membership strictTotalOrder using (_∈_)
  infixl 6 _+ₑ_
  data Expr (s : ⟨Set⟩) : Set (a ⊔ ℓ₂) where
    var  : (name : Key) → name ∈ s → Expr s
    nat  : ℕ → Expr s
    _+ₑ_ : Expr s → Expr s → Expr s

open import Data.String.Properties using (<-strictTotalOrder-≈)
open Definintions (<-strictTotalOrder-≈)
import Data.Tree.AVL.Sets (<-strictTotalOrder-≈) as Sets
open Sets using (⟨Set⟩)

exp₁ : Expr (Sets.fromList ("a" ∷ "b" ∷ "c" ∷ []))
exp₁ = nat 1 +ₑ var "a" +ₑ var "b" +ₑ var "c"
