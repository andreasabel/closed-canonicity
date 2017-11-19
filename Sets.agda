-- Sets in ITT following Aczel, Werner, Barras

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)

open import Function using (id)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

Type : ∀ ℓ → Set (lsuc ℓ)
Type ℓ = Set ℓ

-- Image

data Im {a b} {A : Type a} {B : Type b} (f : A → B) : B → Type a where
  inv : (x : A) → Im f (f x)

-- surjective : ∀ {a b} {A : Type a} {B : Type b} (f : A → B) → Type (a ⊔ b)
-- surjective f = ∀ b → Im f b

surjective : ∀ {a b} {A : Type a} {B : Type b} (f : A → B) → Type (a ⊔ b)
surjective f = ∀ b → ∃ λ a → b ≡ f a

-- Definition of sets, elementhood, and equality
------------------------------------------------------------------------

-- Sets are infinitely branching well-founded trees.
-- The branching type is given at each node.

data set ℓ : Type (lsuc ℓ) where
  sup : ∀{I : Type ℓ} (els : I → set ℓ) → set ℓ

-- Branching type

Br : ∀{ℓ} (a : set ℓ) → Type ℓ
Br (sup {I = I} _) = I

-- Elements

els : ∀{ℓ} (a : set ℓ) (i : Br a) → set ℓ
els (sup f) = f

syntax els a i = a ` i

-- Intensional elementhood

_∈∈_ : ∀{ℓ} (a b : set ℓ) → Type ℓ
a ∈∈ sup f = Im f a -- ∃ λ i → f i ≡ a

-- Equality over intensional elementhood

_≡≡_ : ∀{ℓ} (a b : set ℓ) → Type ℓ
sup f ≡≡ b = ∀ i → f i ∈∈ b

-- Elementhood and extensional equality (recursive)

mutual
  _∈_ : ∀{ℓ} (a b : set ℓ) → Type ℓ
  a ∈ sup f = ∃ λ i → a ≅ f i

  _≅_ : ∀{ℓ} (a b : set ℓ) → Type ℓ
  a ≅ b = (a ⊂ b) × (b ⊂ a)

  _⊂_  : ∀{ℓ} (a b : set ℓ) → Type ℓ
  sup f ⊂ b = ∀ i → f i ∈ b

_∉_ : ∀{ℓ} (a b : set ℓ) → Type ℓ
a ∉ b = ¬ (a ∈ b)

-- Reflexivity

mutual
  ⊂-refl : ∀{ℓ} (a : set ℓ) → a ⊂ a
  ⊂-refl (sup f) i = i , ≅-refl (f i)

  ≅-refl : ∀{ℓ} (a : set ℓ) → a ≅ a
  ≅-refl a = ⊂-refl a , ⊂-refl a

-- Transitivity

mutual
  ⊂-trans : ∀{ℓ} {a b c : set ℓ} (p : a ⊂ b) (q : b ⊂ c) → a ⊂ c
  ⊂-trans {ℓ} {sup f} {sup g} {sup h} p q i = let
      j , d = p i
      k , e = q j
    in k , ≅-trans d e

  ≅-trans : ∀{ℓ} {a b c : set ℓ} (d : a ≅ b) (e : b ≅ c) → a ≅ c
  ≅-trans (p , p') (q , q') = ⊂-trans p q , ⊂-trans q' p'

-- Symmetry

≅-sym : ∀{ℓ} {a b : set ℓ} (p : a ≅ b) → b ≅ a
≅-sym (p , p') = p' , p

-- Introduction and elimination for ∈

∈-intro : ∀{ℓ} {a b : set ℓ} (p : ∃ λ i → a ≅ (b ` i)) → a ∈ b
∈-intro {ℓ} {a} {sup f} p = p

∈-elim : ∀{ℓ} {a b : set ℓ} (p : a ∈ b) → ∃ λ i → a ≅ (b ` i)
∈-elim {ℓ} {a} {sup f} p = p

-- Introduction and elimination for ⊂

⊂-intro : ∀{ℓ} {a b : set ℓ} (cast : ∀ {c} → c ∈ a → c ∈ b) → a ⊂ b
⊂-intro {a = sup f} cast i = cast (i , ≅-refl _)

⊂-elim : ∀{ℓ} {a b c : set ℓ} (q : b ⊂ c) (p : a ∈ b) → a ∈ c
⊂-elim {ℓ} {a} {sup f} {sup g} q (i , d) = let
    j , e = q i
  in j , ≅-trans d e

-- Compatibility of elementhood with subset

∈-cong-⊂ : ∀{ℓ} {a b c : set ℓ} (p : a ∈ b) (q : b ⊂ c) → a ∈ c
∈-cong-⊂ p q = ⊂-elim q p

-- Compatibility of elementhood with equality

∈-congʳ : ∀{ℓ} {a b c : set ℓ} (p : a ∈ b) (e : b ≅ c) → a ∈ c
∈-congʳ p (q , _) = ∈-cong-⊂ p q

∈-congˡ : ∀{ℓ} {a b c : set ℓ} (d : a ≅ b) (q : b ∈ c) → a ∈ c
∈-congˡ {ℓ} {a} {b} {sup f} d (i , e) = i , ≅-trans d e

-- Foundation:  If  a ⊂ b  then  b ∉ a.

found : ∀{ℓ} {a b : set ℓ} (p : a ⊂ b) (q : b ∈ a) → ⊥
found {ℓ} {sup f} {b} p (i , q , _) = found q (p i)

-- Thus, a ∉ a.

irr : ∀{ℓ} {a : set ℓ} → a ∉ a
irr = found (⊂-refl _)

-- Constructions on sets
------------------------------------------------------------------------

-- Empty set

∅ : ∀{ℓ} → set ℓ
∅ {ℓ} = sup {I = Empty} λ()
  where data Empty : Type ℓ where

∅-elim : ∀{ℓ} {c : set ℓ} → c ∉ ∅
∅-elim (() , _)

-- Singleton set

sg : ∀{ℓ} (a : set ℓ) → set ℓ
sg {ℓ} a = sup {I = Unit} λ _ → a
  where record Unit : Type ℓ where

sg-intro : ∀{ℓ} (a : set ℓ) → a ∈ sg a
sg-intro a = _ , ≅-refl a

sg-elim : ∀{ℓ} {c a : set ℓ} (p : c ∈ sg a) → c ≅ a
sg-elim (_ , e) = e

sg-cong : ∀{ℓ} {a b : set ℓ} (e : a ≅ b) → sg a ≅ sg b
sg-cong e = (λ _ → _ , e) , (λ _ → _ , ≅-sym e)

-- Putting two elements into a set
-- Forms {a,b}; not to be confused with the tuple (a,b)

data Two {ℓ} : Type ℓ where
  true false : Two

pair : ∀{ℓ} (a b : set ℓ) → set ℓ
pair a b = sup {I = Two} λ where true → a; false → b

pair-introˡ : ∀{ℓ} {a b : set ℓ} → a ∈ pair a b
pair-introˡ = true , ≅-refl _

pair-introʳ : ∀{ℓ} {a b : set ℓ} → b ∈ pair a b
pair-introʳ = false , ≅-refl _

pair-elim :  ∀{ℓ} {c a b : set ℓ} (p : c ∈ pair a b) → (c ≅ a) ⊎ (c ≅ b)
pair-elim (true  , e) = inj₁ e
pair-elim (false , e) = inj₂ e

pair-cong : ∀{ℓ} {a a' b b' : set ℓ} (p : a ≅ a') (q : b ≅ b') → pair a b ≅ pair a' b'
pair-cong p q = (λ{ true → true , p       ; false → false , q      })
              , (λ{ true → true , ≅-sym p ; false → false , ≅-sym q})

-- Union of two sets

_∪_ : ∀{ℓ} (a b : set ℓ) → set ℓ
a ∪ b = sup λ where
  (inj₁ i) → a ` i
  (inj₂ j) → b ` j

∪-introˡ : ∀{ℓ} {a b c : set ℓ} (p : c ∈ a) → c ∈ (a ∪ b)
∪-introˡ {a = sup f} (i , e) = inj₁ i , e

∪-introʳ : ∀{ℓ} {a b c : set ℓ} (p : c ∈ b) → c ∈ (a ∪ b)
∪-introʳ {b = sup g} (i , e) = inj₂ i , e

∪-elim : ∀{ℓ} {a b c : set ℓ} (p : c ∈ (a ∪ b)) → (c ∈ a) ⊎ (c ∈ b)
∪-elim {a = sup f} (inj₁ i , e) = inj₁ (i , e)
∪-elim {b = sup g} (inj₂ i , e) = inj₂ (i , e)

∪-case : ∀{ℓ} {a b c : set ℓ} (p : c ∈ (a ∪ b)) {q} {Q : Type q} (left : c ∈ a → Q) (right : c ∈ b → Q) → Q
∪-case p left right = [ left , right ]′ (∪-elim p)

∪-split : ∀{ℓ q} {Q : Type q} {a b c : set ℓ} (left : c ∈ a → Q) (right : c ∈ b → Q) (p : c ∈ (a ∪ b)) → Q
∪-split left right p = ∪-case p left right

-- ∪-monˡ : ∀{ℓ} {a a'} (a⊂a' : a ⊂ a') (b : set ℓ) → (a ∪ b) ⊂ (a' ∪ b)
-- ∪-monˡ a⊂a' b = ⊂-intro (∪-split (λ c∈a → ∪-introˡ (⊂-elim a⊂a' c∈a)) ∪-introʳ)

-- ∪-monʳ : ∀{ℓ} a {b b' : set ℓ} (b⊂b' : b ⊂ b') → (a ∪ b) ⊂ (a ∪ b')
-- ∪-monʳ a b⊂b' = ⊂-intro (∪-split ∪-introˡ (λ c∈b → ∪-introʳ (⊂-elim b⊂b' c∈b)))

∪-mon : ∀{ℓ} {a a' b b' : set ℓ} (a⊂a' : a ⊂ a') (b⊂b' : b ⊂ b') → (a ∪ b) ⊂ (a' ∪ b')
∪-mon a⊂a' b⊂b' = ⊂-intro (∪-split (λ c∈a → ∪-introˡ (⊂-elim a⊂a' c∈a))
                                   (λ c∈b → ∪-introʳ (⊂-elim b⊂b' c∈b)))

∪-cong : ∀{ℓ} {a a' b b' : set ℓ} (a≅a' : a ≅ a') (b≅b' : b ≅ b') → (a ∪ b) ≅ (a' ∪ b')
∪-cong (a⊂a' , a'⊂a) (b⊂b' , b'⊂b) = ∪-mon a⊂a' b⊂b' , ∪-mon a'⊂a b'⊂b

-- Union of a family of sets

⋃ : ∀{ℓ} {I : Type ℓ} (f : I → set ℓ) → set ℓ
⋃ {ℓ} {I} f = sup {I = Σ I λ i → Br (f i)} λ p → f (proj₁ p) ` proj₂ p

⋃-intro : ∀{ℓ} {I : Type ℓ} (f : I → set ℓ) {c : set ℓ} {i : I} (p : c ∈ f i) → c ∈ ⋃ f
⋃-intro f {c} {i} p = let
    j , e = ∈-elim p
  in (i , j) , e

⋃-elim : ∀{ℓ} {I : Type ℓ} (f : I → set ℓ) {c : set ℓ} (p : c ∈ ⋃ f) → ∃ λ i → c ∈ f i
⋃-elim _ ((i , j) , e) = i , ∈-intro (j , e)

⋃-mon : ∀{ℓ} {I : Type ℓ} {f f' : I → set ℓ} (p : ∀ i → f i ⊂ f' i) → ⋃ f ⊂ ⋃ f'
⋃-mon {f = f} {f'} p = ⊂-intro λ c∈⋃f → let
    i , q = ⋃-elim f c∈⋃f
  in ⋃-intro f' (⊂-elim (p i) q)

⋃-cong : ∀{ℓ} {I : Type ℓ} {f f' : I → set ℓ} (p : ∀ i → f i ≅ f' i) → ⋃ f ≅ ⋃ f'
⋃-cong p = ⋃-mon (λ i → proj₁ (p i))
          , ⋃-mon (λ i → proj₂ (p i))

-- Predicates over sets (need to respect equality)

IsPred : ∀ {ℓ} (P : set ℓ → Type ℓ) → Type (lsuc ℓ)
IsPred {ℓ} P = ∀{a b : set ℓ} (e : a ≅ b) (p : P a) → P b

record Pred ℓ : Type (lsuc ℓ) where
  constructor pred
  field
    _!_  : set ℓ → Type ℓ
    resp : ∀{a b : set ℓ} (e : a ≅ b) (p : _!_ a) → _!_ b

-- Comprehension (restriction)

_∣_ : ∀{ℓ} (a : set ℓ) (P : set ℓ → Type ℓ) → set ℓ
a ∣ P = sup {I = ∃ λ i → P (a ` i)} λ p → a ` proj₁ p

compr-intro : ∀{ℓ} {a c : set ℓ} {P : set ℓ → Type ℓ} (resp : IsPred P)
  (q : c ∈ a) (p : P c) → c ∈ (a ∣ P)
compr-intro resp q p = let
    i , e = ∈-elim q
  in (i , resp e p) , e

compr-elimˡ : ∀{ℓ} {a c : set ℓ} {P : set ℓ → Type ℓ} (q : c ∈ (a ∣ P)) → c ∈ a
compr-elimˡ ((i , j) , e) = ∈-intro (i , e)

compr-elimʳ : ∀{ℓ} {a c : set ℓ} {P : set ℓ → Type ℓ} (resp : IsPred P) (q : c ∈ (a ∣ P)) → P c
compr-elimʳ resp ((i , j) , e) = resp (≅-sym e) j

-- Intersection of two sets

_∩_ : ∀{ℓ} (a b : set ℓ) → set ℓ
a ∩ b = a ∣ (_∈ b)

∩-intro : ∀{ℓ} {a b c : set ℓ} (p : c ∈ a) (q : c ∈ b) → c ∈ (a ∩ b)
∩-intro p q = let
    i , d = ∈-elim p
  in (i , ∈-congˡ (≅-sym d) q) , d

∩-elimˡ : ∀{ℓ} {a b c : set ℓ} (p : c ∈ (a ∩ b)) → c ∈ a
∩-elimˡ ((i , j) , e) = ∈-intro (i , e)

∩-elimʳ : ∀{ℓ} {a b c : set ℓ} (p : c ∈ (a ∩ b)) → c ∈ b
∩-elimʳ ((i , j) , e) = ∈-congˡ e j

-- Intersection of a non-empty family...

-- Covariant powerset

Pow⁺ : ∀{ℓ} (D : Type ℓ) (a : set ℓ) → set ℓ
Pow⁺ D (sup {I = I} f) = sup λ (sel : D → I) → sup λ (d : D) → f (sel d)

Pow⁺-elim : ∀{ℓ} {D : Type ℓ} {a c : set ℓ} (p : c ∈ Pow⁺ D a) → c ⊂ a
Pow⁺-elim {a = sup f} (sel , e) = ⊂-intro λ q →
  let    i , d = ∈-congʳ q e
  in sel i , d

-- Thanks to proof relevance, we can define Pow⁺-intro!
-- A proof of c ⊂ a contains a function Br c → Br a which we take as selector.

Pow⁺-intro : ∀{ℓ} {a c : set ℓ} (p : c ⊂ a) → c ∈ Pow⁺ (Br c) a
Pow⁺-intro {a = sup g} {c = sup {I = I} f} p =
  (λ i → proj₁ (p i)) ,
  (λ i → _ , proj₂ (p i)) ,
  (λ i → _ , ≅-sym (proj₂ (p i)))

Pow⁺-mon : ∀{ℓ} {D : Type ℓ} {a a' : set ℓ} (a⊂a' : a ⊂ a') → Pow⁺ D a ⊂ Pow⁺ D a'
Pow⁺-mon {a = sup {I = I} f} {sup {I = J} g} a⊂a' sel =
  (λ d → proj₁ (a⊂a' (sel d))) ,
  (λ d → d , proj₂ (a⊂a' (sel d))) ,
  (λ d → d , ≅-sym (proj₂ (a⊂a' (sel d))))

Pow⁺-conv : ∀{ℓ} {D D' : Type ℓ} (h : D' → D) (surj : surjective h) (a : set ℓ) → Pow⁺ D a ⊂ Pow⁺ D' a
Pow⁺-conv h surj (sup {I = I} f) sel =
  (λ d' → sel (h d')) ,
  (λ d → let d' , d≡hd' = surj d in d' , subst (λ z → f (sel d) ≅ f (sel z)) d≡hd' (≅-refl _)) ,
  λ d' → h d' , ≅-refl _

-- Pow⁺-mon : ∀{ℓ} {D D' : Type ℓ} (h : D' → D) {a a' : set ℓ} (a⊂a' : a ⊂ a') → Pow⁺ D a ⊂ Pow⁺ D' a'
-- Pow⁺-mon h {sup {I = I} f} {sup {I = J} g} a⊂a' sel =
--   (λ d' → proj₁ (a⊂a' (sel (h d')))) ,
--   (λ d → let (j , e) = a⊂a' (sel d) in {!!}) ,
--   λ d' → {!a⊂a' (sel (h d')) , ?!}

-- Countable powerset

data Nat ℓ : Type ℓ where
  zero : Nat ℓ
  suc  : (n : Nat ℓ) → Nat ℓ

Pω : ∀{ℓ} (a : set ℓ) → set ℓ
Pω {ℓ} a = Pow⁺ (Nat ℓ) a
