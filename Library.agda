
open import Level            public using (Level; _⊔_; Lift; lower) renaming (zero to lzero; suc to lsuc)

open import Data.Empty       public using (⊥; ⊥-elim)
open import Data.Unit        public using (⊤)
open import Data.Nat.Base    public using (ℕ; zero; suc; _+_)
open import Data.Nat.GeneralisedArithmetic
                             public using (fold)
open import Data.Maybe       public using (Maybe; nothing; just; maybe)
open import Data.Product     public using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum         public using (_⊎_; inj₁; inj₂; [_,_]′; [_,_])

open import Function         public using (id; _$_; _∘_)

open import Relation.Nullary public using (¬_)
open import Relation.Binary.PropositionalEquality
                             public using (_≡_; subst)
open import Induction.WellFounded
                             public using (Acc; acc)

Type : ∀ ℓ → Set (lsuc ℓ)
Type ℓ = Set ℓ
