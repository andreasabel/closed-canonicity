{-# OPTIONS --caching #-}
{-# OPTIONS --postfix-projections #-}

-- Sets in ITT following Aczel, Werner, Barras

open import Library

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

lift-set : ∀{a ℓ} → set ℓ → set (a ⊔ ℓ)
lift-set {a} (sup {I = I} f) = sup {I = Lift a I} λ i → lift-set {a} (f (lower i))

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

_≇_ : ∀{ℓ} (a b : set ℓ) → Type ℓ
a ≇ b = ¬ (a ≅ b)

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

-- Predicates over sets (need to respect equality)

IsPred : ∀ {ℓ} (P : set ℓ → Type ℓ) → Type (lsuc ℓ)
IsPred {ℓ} P = ∀{a b : set ℓ} (e : a ≅ b) (p : P a) → P b

record Pred ℓ : Type (lsuc ℓ) where
  constructor pred
  field
    _!_  : set ℓ → Type ℓ
    resp : IsPred _!_


-- ∈ induction.

∈-ind : ∀{ℓ} {P} → IsPred P
      → (f : ∀ (a : set ℓ) → (∀ {b} → b ∈ a → P b) → P a)
      → ∀ a → P a
∈-ind P-transp f a@(sup ela) = f a λ where
  (i , eqv) → P-transp (≅-sym eqv) (∈-ind P-transp f (ela i))


-- Get a selection function from ⊂

sel-from-⊂ : ∀{ℓ} {a b : set ℓ} (p : a ⊂ b) → Br a → Br b
sel-from-⊂ {a = sup f} {b = sup g} p i = proj₁ (p i)

-- Restriction by selecting elements

select : ∀{ℓ} (a : set ℓ) {D : Type ℓ} (sel : D → Br a) → set ℓ
select (sup f) sel = sup λ d → f (sel d)

select-elim : ∀{ℓ} (a : set ℓ) {D : Type ℓ} (sel : D → Br a) → select a sel ⊂ a
select-elim (sup f) sel d = sel d , ≅-refl _

select-sel : ∀{ℓ} {a b : set ℓ} (p : a ⊂ b) → select b (sel-from-⊂ p) ≅ a
select-sel {a = sup f} {b = sup g} p =
  (λ i → i , ≅-sym (proj₂ (p i))) ,
  (λ i → i , proj₂ (p i))

-- Constructions on sets
------------------------------------------------------------------------

-- Empty set

∅ : ∀{ℓ} → set ℓ
∅ {ℓ} = sup {I = Empty} λ()
  where data Empty : Type ℓ where

IsEmpty : ∀{ℓ} (a : set ℓ) → Type (lsuc ℓ)
IsEmpty {ℓ} a = ∀ {c : set ℓ} → c ∉ a

∅-elim : ∀{ℓ} → IsEmpty (∅ {ℓ})
∅-elim (() , _)

IsInhabited : ∀{ℓ} (a : set ℓ) → Type (lsuc ℓ)
IsInhabited a = ∃ λ c → c ∈ a

emptyNotInhabited : ∀{ℓ} {a : set ℓ} → IsEmpty a → ¬ IsInhabited a
emptyNotInhabited p (c , q) = p q

inhabitedNotEmpty : ∀{ℓ} {a : set ℓ} → IsInhabited a → ¬ IsEmpty a
inhabitedNotEmpty (c , q) p = p q

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

sg-inhabited : ∀{ℓ} {a : set ℓ} → IsInhabited (sg a)
sg-inhabited {a = a} = a , sg-intro a

SubSingleton : ∀{ℓ} (a b : set ℓ) → Type ℓ
SubSingleton a b = a ⊂ sg b

IsSg : ∀{ℓ} (a : set ℓ) → Type (lsuc ℓ)
IsSg a = ∃ λ b → a ≅ sg b

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

pair-inhabited : ∀{ℓ} {a b : set ℓ} → IsInhabited (pair a b)
pair-inhabited {a = a} = a , true , ≅-refl a

-- Union of two sets

_∪_ : ∀{ℓ} (a b : set ℓ) → set ℓ
a ∪ b = sup {I = _ ⊎ _} λ where
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

⋃ᶠ : ∀{ℓ} {I : Type ℓ} (f : I → set ℓ) → set ℓ
⋃ᶠ {ℓ} {I} f = sup {I = Σ I λ i → Br (f i)} λ p → f (proj₁ p) ` proj₂ p

⋃ᶠ-intro : ∀{ℓ} {I : Type ℓ} (f : I → set ℓ) {c : set ℓ} {i : I} (p : c ∈ f i) → c ∈ ⋃ᶠ f
⋃ᶠ-intro f {c} {i} p = let
    j , e = ∈-elim p
  in (i , j) , e

⋃ᶠ-elim : ∀{ℓ} {I : Type ℓ} (f : I → set ℓ) {c : set ℓ} (p : c ∈ ⋃ᶠ f) → ∃ λ i → c ∈ f i
⋃ᶠ-elim _ ((i , j) , e) = i , ∈-intro (j , e)

⋃ᶠ-mon : ∀{ℓ} {I : Type ℓ} {f f' : I → set ℓ} (p : ∀ i → f i ⊂ f' i) → ⋃ᶠ f ⊂ ⋃ᶠ f'
⋃ᶠ-mon {f = f} {f'} p = ⊂-intro λ c∈⋃ᶠf → let
    i , q = ⋃ᶠ-elim f c∈⋃ᶠf
  in ⋃ᶠ-intro f' (⊂-elim (p i) q)

⋃ᶠ-cong : ∀{ℓ} {I : Type ℓ} {f f' : I → set ℓ} (p : ∀ i → f i ≅ f' i) → ⋃ᶠ f ≅ ⋃ᶠ f'
⋃ᶠ-cong p = ⋃ᶠ-mon (λ i → proj₁ (p i))
          , ⋃ᶠ-mon (λ i → proj₂ (p i))

-- Union of a set of sets

⋃ : ∀{ℓ} (a : set ℓ) → set ℓ
⋃ (sup f) = ⋃ᶠ f

⋃-intro : ∀{ℓ} {a b : set ℓ} (p : b ∈ a) → b ⊂ ⋃ a
⋃-intro {a = sup f} (i , b≅fi) = ⊂-intro λ c∈b → let
    j , d = ∈-elim (∈-congʳ c∈b b≅fi)
  in (i , j) , d

⋃-elim : ∀{ℓ} {a c : set ℓ} (p : c ∈ ⋃ a) → ∃ λ b → (b ∈ a) × (c ∈ b)
⋃-elim {a = sup f} ((i , j) , e) = f i , (i , ≅-refl _) , ∈-intro (j , e)


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

⋂ᶠ : ∀{ℓ} {I : Type ℓ} (i : I) (f : I → set ℓ) → set ℓ
⋂ᶠ i f = f i ∣ λ a → ∀ i′ → a ∈ f i′

⋂ᶠ-intro : ∀{ℓ} {I : Type ℓ} {i : I} {f : I → set ℓ} {a} (r : ∀ j → a ∈ f j) → a ∈ ⋂ᶠ i f
⋂ᶠ-intro {i = i} r = let
    k , p = ∈-elim (r i)
  in (k , λ j → ∈-congˡ (≅-sym p) (r j)) , p

-- Intersection of an inhabited set

⋂ : ∀{ℓ} (a : set ℓ) (inh : IsInhabited a) → set ℓ
⋂ (sup f) (b , i , b≅fi) = ⋂ᶠ i f

_∈∀∈_ : ∀{ℓ} (a b : set ℓ) → Set (lsuc ℓ)
c ∈∀∈ a = ∀ {b} → b ∈ a → c ∈ b

⋂-intro : ∀{ℓ} {a : set ℓ} {inh : IsInhabited a} {c} (r : c ∈∀∈ a) → c ∈ ⋂ a inh
⋂-intro {a = sup f} {b , i , b≅fi} r = ⋂ᶠ-intro λ j → r (j , ≅-refl _)

-- Covariant powerset

-- Pow⁺ : ∀{k ℓ} (D : Type k) (a : set ℓ) → set (k ⊔ ℓ)
-- Pow⁺ {k} {ℓ} D (sup {I = I} f) = sup λ (sel : D → I) → sup λ (d :  Lift {k}{ℓ} D) → lift-set {k} (f (sel (lower d)))

-- Power⁺ : ∀{ℓ} (a : set ℓ) → set (suc ℓ)
-- Power⁺ (sup {I = I} f) = sup {I = I → Type ℓ}

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

-- Ordered pairs / tuples (Kazimierz Kuratowski, 1921)

tup : ∀{ℓ} (a b : set ℓ) → set ℓ
tup a b = pair (sg a) (pair a b)

-- The first argument is member of both components of the Kuratowski pair

fst-in-all-tup : ∀{ℓ} {a b : set ℓ} → a ∈∀∈ tup a b
fst-in-all-tup (true  , _ , p) = p _
fst-in-all-tup (false , _ , p) = p true

-- First projection
-- π₁(p) = ⋃ ⋂ p

fst : ∀{ℓ} (c : set ℓ) (inh : IsInhabited c) → set ℓ
fst c inh = ⋃ (⋂ c inh)

fst-tup-sub : ∀{ℓ} {a b : set ℓ} → fst (tup a b) pair-inhabited ⊂ a
fst-tup-sub ((record {} , f) , i) = ∈-intro (i , ≅-refl _)

fst-tup-sup : ∀{ℓ} {a b : set ℓ} → a ⊂ fst (tup a b) pair-inhabited
fst-tup-sup = ⊂-intro λ c∈a → let
    i , p = ∈-elim c∈a
  in ((_ , \{ true → _ , ≅-refl _ ; false → true , ≅-refl _ }) , i) , p

fst-tup : ∀{ℓ} {a b : set ℓ} → fst (tup a b) (pair-inhabited) ≅ a
fst-tup = fst-tup-sub , fst-tup-sup

-- Second projection
-- π₂ (p) = ⋃ { x ∈ ⋃ p ∣ ⋃ p ≠ ⋂ p → x ∉ ⋂ p }

snd : ∀{ℓ} (c : set ℓ) (inh : IsInhabited c) → set ℓ
snd c inh = let
    u = ⋃ c
    i = ⋂ c inh
  in ⋃ (u ∣ λ a → u ≇ i → a ∉ i)

snd-tup-sub : ∀{ℓ} {a b : set ℓ} → snd (tup a b) pair-inhabited ⊂ b
snd-tup-sub {ℓ} {a} {b} (((true  , _) , y) , p) = {!!}
snd-tup-sub {ℓ} {a} {b} (((false , q) , y) , p) = {!!}

snd-tup-sup : ∀{ℓ} {a b : set ℓ} → b ⊂ snd (tup a b) pair-inhabited
snd-tup-sup = ⊂-intro λ c∈b → let
    i , p = ∈-elim c∈b
  in {!!}

snd-tup : ∀{ℓ} {a b : set ℓ} → snd (tup a b) (pair-inhabited) ≅ b
snd-tup = snd-tup-sub , snd-tup-sup


-- c is a transitive set if a ∈ b ∈ c implies a ∈ c.

TransitiveSet : ∀{ℓ} (c : set ℓ) → Set (lsuc ℓ)
TransitiveSet c = ∀{b} → b ∈ c → b ⊂ c

-- "transitive set" is an extensional notion.

transitive-ext : ∀{ℓ} {b c : set ℓ} → b ≅ c → TransitiveSet b → TransitiveSet c
transitive-ext (b⊂c , c⊂b) t p = ⊂-trans (t (⊂-elim c⊂b p)) b⊂c

-- Ordinals are transitive sets of transitive elements.

record Ordinal {ℓ} (α : set ℓ) : Set (lsuc ℓ) where
  constructor ordinal
  field
    isTrans : TransitiveSet α
    elTrans : ∀{β} → β ∈ α → TransitiveSet β
open Ordinal

-- Von Neumann successor: α + 1 = α ∪ {α}.

osuc : ∀{ℓ} (α : set ℓ) → set ℓ
osuc α@(sup {I = I} f) = sup {I = Maybe I} (maybe f α)

-- α ∈ α + 1

osuc-intro-∈ : ∀{ℓ} (α : set ℓ) → α ∈ osuc α
osuc-intro-∈ (sup f) = nothing , ≅-refl (sup f)

-- α ⊂ α + 1

osuc-intro-⊂ : ∀{ℓ} (α : set ℓ) → α ⊂ osuc α
osuc-intro-⊂ (sup f) i = just i , ≅-refl (f i)

-- β ⊂ α  implies  β ⊂ osuc α

osuc-intro-⊂' : ∀{ℓ} {α β : set ℓ} → β ⊂ α → β ⊂ osuc α
osuc-intro-⊂' p = ⊂-trans p (osuc-intro-⊂ _)

-- If  β ∈ α + 1  then  β ∈ α  or  β ≅ α.

osuc-elim : ∀{ℓ}{α β : set ℓ} (p : β ∈ osuc α) → (β ∈ α) ⊎ (β ≅ α)
osuc-elim {α = sup f} (just i  , p) = inj₁ (i , p)
osuc-elim {α = sup f} (nothing , p) = inj₂ p

osuc-case : ∀{ℓ }{α β : set ℓ} (p : β ∈ osuc α) → ∀{c} {C : Type c} → (β ∈ α → C) → (β ≅ α → C) → C
osuc-case {α = sup f} (just i  , p) k₁ k₂ = k₁ (i , p)
osuc-case {α = sup f} (nothing , p) k₁ k₂ = k₂ p

osuc-copair : ∀{ℓ c} {α β : set ℓ} {C : Type c}
  → (β ∈ α → C)
  → (β ≅ α → C)
  → β ∈ osuc α → C
osuc-copair {α = sup f} k₁ k₂ (just i  , p) = k₁ (i , p)
osuc-copair {α = sup f} k₁ k₂ (nothing , p) = k₂ p

-- If α is transitive, so is α + 1.

transitive-suc : ∀{ℓ} {α : set ℓ} (t : TransitiveSet α) → TransitiveSet (osuc α)
transitive-suc t = osuc-copair (osuc-intro-⊂' ∘ t) (osuc-intro-⊂' ∘ proj₁)

-- If α is an ordinal, so is α + 1.

ordinal-suc : ∀{ℓ} {α : set ℓ} (o : Ordinal α) → Ordinal (osuc α)
ordinal-suc o .isTrans = transitive-suc (o .isTrans)
ordinal-suc o .elTrans = osuc-copair
  (λ β∈α → o .elTrans β∈α )
  (λ β≅α → transitive-ext (≅-sym β≅α) (o .isTrans))

-- If f is a family of transitive sets, so is the union ⋃ f.

transitive-union : ∀{ℓ} {I : Type ℓ} (f : I → set ℓ) (t : ∀ i → TransitiveSet (f i)) → TransitiveSet (⋃ᶠ f)
transitive-union f t p = let
    (i , q) = ⋃ᶠ-elim f p
  in
    ⊂-trans (t i q) (⊂-intro (⋃ᶠ-intro f))

-- If f is a family of ordinals, so is the union ⋃ f.

ordinal-union : ∀{ℓ} {I : Type ℓ} (f : I → set ℓ) (t : ∀ i → Ordinal (f i)) → Ordinal (⋃ᶠ f)
ordinal-union f t .isTrans   = transitive-union f (isTrans ∘ t)
ordinal-union f t .elTrans p = let
    (i , q) = ⋃ᶠ-elim f p
  in
    t i .elTrans q

-- -}
-- -}
-- -}
