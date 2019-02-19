{-# OPTIONS --postfix-projections #-}

-- Plump ordinals following Mike Shulman's blog post.
-- See https://homotopytypetheory.org/2014/02/22/surreals-plump-ordinals/

open import Library
open import Data.W
open import Data.Container.Core

data Ord ℓ : Type (lsuc ℓ) where
  sup : ∀{I : Type ℓ} (f : I → Ord ℓ) → Ord ℓ

variable
  ℓ : Level
  α β γ α' : Ord ℓ
  I : Type ℓ
  i j : I
  f g : I → Ord ℓ
  n m : ℕ

-- Branching type.

Br : Ord ℓ → Type ℓ
Br (sup {I = I} _) = I

-- Picking a predecessor.

_`_ : (α : Ord ℓ) → Br α → Ord ℓ
sup f ` i = f i

-- α < β  iff  (∃i. α ≤ βᵢ)
-- α ≤ β  iff  (∀i. αᵢ < β)
-- α = β  iff  α ≤ β ≤ α

mutual
  _<_ : (α β : Ord ℓ) → Type ℓ
  α < sup f = ∃ λ i → α ≤ f i

  _≤_ : (α β : Ord ℓ) → Type ℓ
  sup f ≤ β = ∀ i → f i < β

_≅_ : (α β : Ord ℓ) → Type ℓ
α ≅ β = (α ≤ β) × (β ≤ α)

_≥_ : (α β : Ord ℓ) → Type ℓ
α ≥ β = β ≤ α

-- Predecessor.

pred-intro-left : α ≤ β → (α ` i) < β
pred-intro-left {α = sup f} h = h _

pred-intro-right : α < β → ∃ λ i → α ≤ (β ` i)
pred-intro-right {β = sup f} p = p

pred-< : α ≤ (β ` i) → α < β
pred-< {β = sup f} p = _ , p

-- Reflexivity.

refl-≤ : α ≤ α
refl-≤ {α = sup f} i = i , refl-≤

refl-≅ : α ≅ α
refl-≅ = refl-≤ , refl-≤

-- Symmetry.

sym-≅ : α ≅ β → β ≅ α
sym-≅ (p , q) = (q , p)

-- Embedding of < into ≤.

mutual
  sup-< : sup f < β → f i < β
  sup-< {β = sup g} (i , h) = i , ≤-from-< (h _)

  ≤-from-< : α < β → α ≤ β
  ≤-from-< {α = sup f} {β} p i = sup-< p

-- Transitivity.

mutual
  trans-<-≤ : α < β → β ≤ γ → α < γ
  trans-<-≤ {β = sup f} (i , p) h = trans-≤-< p (h i)

  trans-≤-< : α ≤ β → β < γ → α < γ
  trans-≤-< {γ = sup f} p (i , q) = i , trans-≤-≤ p q

  trans-≤-≤ : α ≤ β → β ≤ γ → α ≤ γ
  trans-≤-≤ {α = sup f} h q i = trans-<-≤ (h i) q

trans-<-< : α < β → β < γ → α < γ
trans-<-< p = trans-<-≤ p ∘ ≤-from-<
-- trans-<-< {γ = sup f} p (i , q) = i , ≤-from-< (trans-<-≤ p q)

trans-≅ : α ≅ β → β ≅ γ → α ≅ γ
trans-≅ (p , p') (q , q') = trans-≤-≤ p q , trans-≤-≤ q' p'

-- Well-foundedness.

-- Antitonicity of accessibility.

acc-≤ : β ≤ α → Acc _<_ α → Acc _<_ β
acc-≤ β≤α (acc h) = acc λ γ γ<β → h γ (trans-<-≤ γ<β β≤α)

-- Well-foundedness of _<_.

wf : Acc _<_ α
wf {α = sup f} = acc λ _ p → acc-≤ (proj₂ p) wf

acc-sup : (∀ i → Acc _<_ (f i)) → Acc _<_ (sup f)
acc-sup h = acc (λ γ p → let (i , γ≤fi) = p in acc-≤ γ≤fi (h i))

-- Zero ordinal

∅ : Ord ℓ
∅ = sup {I = Lift _ ⊥} λ()

-- Zero as a predicate on ordinals
-- (rather pointless enterprise).

OZero : Ord ℓ → Type ℓ
OZero α = ¬ Br α

isZero-∅ : ∀{ℓ} → OZero {ℓ = ℓ} ∅
isZero-∅ ()

oZero-is-∅ : OZero α → α ≤ ∅
oZero-is-∅ {α = sup f} p i = ⊥-elim (p i)

oZero-least : α < β → OZero β → ⊥
oZero-least {β = sup g} (i , p) q = q i

oZero-downward : α ≤ β → OZero β → OZero α
oZero-downward {α = sup f} p q i = oZero-least (p i) q

oZero-intro : α ≤ ∅ → OZero α
oZero-intro p = oZero-downward p isZero-∅

-- Successor.

osuc : Ord ℓ → Ord ℓ
osuc α = sup {I = Lift _ ⊤} λ _ → α

osuc-< : α < osuc α
osuc-< = _ , refl-≤

-- If  α ≤ β  then  α < β+1.

osuc-≤-< : α ≤ β → α < osuc β
osuc-≤-< p = _ , p

-- If  α < β  then  α+1 ≤ β.

osuc-<-≤ : α < β → osuc α ≤ β
osuc-<-≤ {β = sup g} p _ = p

-- As a consequence, the successor preserves < and ≤.

-- If  α < β  then  α + 1 < β + 1.

osuc-cong-< : α < β → osuc α < osuc β
osuc-cong-< = osuc-≤-< ∘ osuc-<-≤
-- osuc-cong-< {α = sup f} {β = sup g} (j , h) = nothing , maybe (λ i → j , ≤-from-< (h i)) (j , h)

-- If  α ≤ β  then  α + 1 ≤ β + 1.
--
-- Show  (α+1)[i] ≤ β+1  for all i.
-- Case i=nothing. Show α ≤ β + 1.  Follows from α ≤ β
-- Case just i.    Show α[i] ≤ β + 1.

osuc-cong-≤ : α ≤ β → osuc α ≤ osuc β
osuc-cong-≤ = osuc-<-≤ ∘ osuc-≤-<
-- osuc-cong-≤ {α = sup f} {β = sup g} h (just i) = let (j , p) = h i in just j , p
-- osuc-cong-≤ {α = sup f} {β = sup g} h nothing  = nothing , h


-- Successor as a relation on ordinals
-- FAILED ATTEMPT

_OSucOf_ : (α β : Ord ℓ) → Type ℓ
sup {I = I} f OSucOf β = I × ∀ i → f i ≅ β

oSucOf-osuc : osuc α OSucOf α
oSucOf-osuc {α = sup f} = _ , λ _ → refl-≅

oSucOf-subst-l : α ≅ β → α OSucOf γ → β OSucOf γ
oSucOf-subst-l {α = sup f} {β = sup {I = J} g} (p₁ , p₂) (i , q) =
  let (j  , p₁') = p₁ i  in j , λ j' →
  let (i' , p₂') = p₂ j' in trans-≤-≤ p₂' (proj₁ (q i')) , {!trans-≤-≤ ? p₁'!}
-- NOT PROVABLE!
--
--  let (i , q') = p' i' in trans-≤-≤ q' (proj₁ (q i)) ,  trans-≤-≤ (proj₂ (q i)) {!p i!}


-- Union (the actual least upper bound).

⋃ : {I : Type ℓ} (f : I → Ord ℓ) → Ord ℓ
⋃ {I = I} f = sup {I = Σ I (Br ∘ f)} λ p → let (i , j) = p in f i ` j

⋃-left : (∀ i → f i ≤ β) → ⋃ f ≤ β
⋃-left h (i , j) = pred-intro-left (h i)

⋃-right : α ≤ g j → α ≤ ⋃ g
⋃-right {α = sup f} {j = j} h i = let
    k , p = pred-intro-right (h i)
  in
    (j , k) , p

-- Relation between ⋃ and sup.

⋃≤sup : ⋃ f ≤ sup f
⋃≤sup {f = f} (i , j) = i , ≤-from-< (pred-intro-left (refl-≤ {α = f i}))

⋃suc≤sup : ⋃ (osuc ∘ f) ≤ sup f
⋃suc≤sup (i , _) = i , refl-≤
-- ⋃suc≤sup {f = f} (i , _) = i , refl-≤ {α = f i}

sup≤⋃suc : sup f ≤ ⋃ (osuc ∘ f)
sup≤⋃suc i = (i , _) , refl-≤

-- "sup" f  is actually  ⋃ { f i + 1 | i : I }

sup=⋃suc : sup f ≅ ⋃ (osuc ∘ f)
sup=⋃suc = sup≤⋃suc , ⋃suc≤sup

-- Lifting

lift : ∀ a → Ord ℓ → Ord (ℓ ⊔ a)
lift a (sup {I = I} f) = sup {I = Lift a I} (lift a ∘ f ∘ lower)

-- An ordinal beyond any α : Ord ℓ

Ω : ∀ ℓ → Ord (lsuc ℓ)
Ω ℓ = sup {I = Ord ℓ} (lift (lsuc ℓ))

-- Ω ℓ is inaccessible for Ord ℓ

inacc : ∀ (α : Ord ℓ) → lift (lsuc ℓ) α < Ω ℓ
inacc α = α , refl-≤

-- Ordinary ordinal addition (recursion on second argument) ?

-- The following definition is nonsense, as α + β ≅ β
-- _+_ : (α β : Ord ℓ) → Ord ℓ
-- α + sup f = sup λ i → α + f i

-- Hessenberg sum (natural sum)

_⊕_ : (α β : Ord ℓ) → Ord ℓ
α@(sup{I = I}f) ⊕ β@(sup{I = J}g) = sup {I = I ⊎ J} [ (λ i → f i ⊕ β) , (λ j → α ⊕ g j) ]′

-- Left monotonicity:  If α ≤ β then α ⊕ γ ≤ β ⊕ γ.

mon-⊕-l : α ≤ β → (α ⊕ γ) ≤ (β ⊕ γ)
mon-⊕-l {α = sup f} {β = sup {I = J} g} {γ = sup {I = K} h} p (inj₁ i) = let (j , q) = p i in
                                                                         inj₁ j , mon-⊕-l q
mon-⊕-l {α = sup f} {β = sup {I = J} g} {γ = sup {I = K} h} p (inj₂ k) = inj₂ k , mon-⊕-l p

-- Right monotonicity.

mon-⊕-r : α ≤ β → (γ ⊕ α) ≤ (γ ⊕ β)
mon-⊕-r {α = sup f} {β = sup {I = J} g} {γ = sup {I = K} h} p (inj₂ i) = let (j , q) = p i in
                                                                         inj₂ j , mon-⊕-r q
mon-⊕-r {α = sup f} {β = sup {I = J} g} {γ = sup {I = K} h} p (inj₁ k) = inj₁ k , mon-⊕-r p

-- Left congruence.

cong-⊕-l : α ≅ β → (α ⊕ γ) ≅ (β ⊕ γ)
cong-⊕-l (α≤β , β≤α) = mon-⊕-l α≤β , mon-⊕-l β≤α

-- Right congruence.

cong-⊕-r : α ≅ β → (γ ⊕ α) ≅ (γ ⊕ β)
cong-⊕-r (α≤β , β≤α) = mon-⊕-r α≤β , mon-⊕-r β≤α

-- Associativity

assoc-⊕-≤ : ((α ⊕ β) ⊕ γ) ≤ (α ⊕ (β ⊕ γ))
assoc-⊕-≤ {α = sup f} {β = sup g} {γ = sup h} (inj₁ (inj₁ i)) = inj₁ i        , assoc-⊕-≤
assoc-⊕-≤ {α = sup f} {β = sup g} {γ = sup h} (inj₁ (inj₂ j)) = inj₂ (inj₁ j) , assoc-⊕-≤
assoc-⊕-≤ {α = sup f} {β = sup g} {γ = sup h} (inj₂ k       ) = inj₂ (inj₂ k) , assoc-⊕-≤

assoc-⊕-≥ : ((α ⊕ β) ⊕ γ) ≥ (α ⊕ (β ⊕ γ))
assoc-⊕-≥ {α = sup f} {β = sup g} {γ = sup h} (inj₁ i       ) = inj₁ (inj₁ i) , assoc-⊕-≥
assoc-⊕-≥ {α = sup f} {β = sup g} {γ = sup h} (inj₂ (inj₁ j)) = inj₁ (inj₂ j) , assoc-⊕-≥
assoc-⊕-≥ {α = sup f} {β = sup g} {γ = sup h} (inj₂ (inj₂ k)) = inj₂ k        , assoc-⊕-≥

assoc-⊕ : ((α ⊕ β) ⊕ γ) ≅ (α ⊕ (β ⊕ γ))
assoc-⊕ = assoc-⊕-≤ , assoc-⊕-≥

-- Commutativity

comm-⊕-≤ : (α ⊕ β) ≤ (β ⊕ α)
comm-⊕-≤ {α = sup f} {β = sup g} (inj₁ i) = inj₂ i , comm-⊕-≤
comm-⊕-≤ {α = sup f} {β = sup g} (inj₂ j) = inj₁ j , comm-⊕-≤

-- ∅ is left unit for ⊕

zero⊕-≤ : (∅ ⊕ β) ≤ β
zero⊕-≤ {β = sup g} (inj₁ ())
zero⊕-≤ {β = sup g} (inj₂ i) = i , zero⊕-≤ {β = g i}
-- zero⊕-≤ {β = sup g} = [ (λ()) , (λ i → i , zero⊕-≤ {β = g i}) ]

zero⊕-≥ : β ≤ (∅ ⊕ β)
zero⊕-≥ {β = sup g} i = inj₂ i , zero⊕-≥

zero⊕ : (∅ ⊕ β) ≅ β
zero⊕ = zero⊕-≤ , zero⊕-≥

-- ∅ is right unit for ⊕  (or just get is by commutativity)

⊕zero-≤ : (α ⊕ ∅) ≤ α
⊕zero-≤ {α = sup g} (inj₂ ())
⊕zero-≤ {α = sup g} (inj₁ i) = i , ⊕zero-≤ {α = g i}

⊕zero-≥ : α ≤ (α ⊕ ∅)
⊕zero-≥ {α = sup g} i = inj₁ i , ⊕zero-≥

⊕zero : (α ⊕ ∅) ≅ α
⊕zero = ⊕zero-≤ , ⊕zero-≥

-- Successor under sum.

suc⊕-≥ : osuc (α ⊕ β) ≤ (osuc α ⊕ β)
suc⊕-≥ {α = sup f} {β = sup g} _ = inj₁ _ ,
  [ (λ i → inj₁ i , refl-≤)
  , (λ i → inj₂ i , refl-≤)
  ]

suc⊕-≤ : (osuc α ⊕ β) ≤ osuc (α ⊕ β)
suc⊕-≤ {α = sup f} {β = sup g} (inj₁ _) = _ ,
  [ (λ i → inj₁ i , refl-≤)
  , (λ i → inj₂ i , refl-≤)
  ]
suc⊕-≤ {α = sup f} {β = sup g} (inj₂ i) = _ ,
  trans-≤-≤ (suc⊕-≤ {α = sup f} {β = g i})
            λ _ → inj₂ i , refl-≤

suc⊕-≅ : (osuc α ⊕ β) ≅ osuc (α ⊕ β)
suc⊕-≅ = suc⊕-≤ , suc⊕-≥


-- Finite ordinals.

data _IsNat_ (α : Ord ℓ) : ℕ → Type (lsuc ℓ) where
  isZero : (p : α ≅ ∅) → α IsNat 0
  isSuc  : ∀{β n} (p : α ≅ osuc β) (q : β IsNat n) → α IsNat (suc n)

-- IsNat is a predicate on ordinals (invariant under ≅).

isNat-subst' : α ≅ β → β IsNat m → α IsNat m
isNat-subst' α≅β (isZero β≅∅)    = isZero (trans-≅ α≅β β≅∅)
isNat-subst' α≅β (isSuc β≅γ+1 q) = isSuc (trans-≅ α≅β β≅γ+1) q

isNat-subst : α ≅ β → α IsNat m → β IsNat m
isNat-subst α≅β = isNat-subst' (sym-≅ α≅β)

-- Natural sum is extension of sum of natural numbers.

⊕-natural : α IsNat n → β IsNat m → (α ⊕ β) IsNat (n + m)
⊕-natural (isZero α≅∅)    q = isNat-subst' (trans-≅ (cong-⊕-l α≅∅) zero⊕) q
⊕-natural (isSuc α≅β+1 p) q = isSuc (trans-≅ (cong-⊕-l α≅β+1) suc⊕-≅) (⊕-natural p q)


-- Constructing ordinals

-- Countable limits

olim : (ℕ → Ord ℓ) → Ord ℓ
olim f = sup {I = Lift _ ℕ} (f ∘ lower)

-- Finite ordinals

ofin : ℕ → Ord ℓ
ofin zero    = ∅
ofin (suc n) = osuc (ofin n)

-- First infinite ordinal

ω : Ord ℓ
ω = olim ofin

-- ω + n

ω+ : ℕ → Ord ℓ
ω+ zero    = ω
ω+ (suc n) = osuc (ω+ n)

-- α + n

_+ℕ_ : Ord ℓ → ℕ → Ord ℓ
α +ℕ zero = α
α +ℕ (suc n) = osuc (α +ℕ n)

-- α +ω

_+ω : Ord ℓ → Ord ℓ
α +ω = olim (α +ℕ_)

-- ω ∙ n

ω∙_ : ℕ → Ord ℓ
ω∙ zero    = ∅
ω∙ (suc n) = (ω∙ n) +ω

-- ω²

ω² : Ord ℓ
ω² = olim ω∙_

-- ORDINALS IN TYPE THEORY
-- Thierry Coquand, Peter Hancock and Anton Setzer
-- Aarhus, August 1997

-- Limit structures

record Lim (X : Type ℓ) : Type ℓ where
  constructor limStruct
  field
    z : X
    s : X → X
    l : (ℕ → X) → X
  omega : X
  omega = l (fold z s)

oLim : Lim (Ord ℓ)
oLim = limStruct ∅ osuc olim

a'Lim : Lim (Ord ℓ → Ord ℓ)
a'Lim = limStruct id (osuc ∘_) (λ f α → olim λ n → f n α)

a₁Lim : Lim (Ord ℓ → Ord ℓ)
a₁Lim = limStruct osuc (λ g α → olim λ n → fold id (g ∘_) n α) (λ f α → olim λ n → f n α)

ω^ω : Ord ℓ
ω^ω = Lim.omega a₁Lim ∅  -- ??


-- _+ω² : Ord ℓ → Ord ℓ
-- α +ω² =  sup {I = Lift _ ℕ} (α +ℕ_ ∘ ω∙_ ∘ lower)

-- ω² ∙ n

ω²∙_ : ℕ → Ord ℓ
ω²∙ zero    = ∅
ω²∙ (suc n) = ω²∙ n

-- ωⁿ

ω^_ : ℕ → Ord ℓ
ω^ zero = ω
ω^ (suc n) = ω^ n


-- Closure ordinals for W-types.

module _ (A : Set ℓ) (B : A → Set ℓ) where

  -- The ordinal height of a tree.

  o : W (A ▷ B) → Ord ℓ
  o (sup (a , f)) = sup {I = B a} (o ∘ f)

  -- A closure ordinal for W A B is a strict upper bound
  -- on the height of any possible tree.

  IsClosure : (γ : Ord ℓ) → Type ℓ
  IsClosure γ = ∀ (w : W (A ▷ B)) → o w < γ

  -- The closure ordinal is literally constructed as the
  -- strict upper bound on all tree heights.

  closure : Ord ℓ
  closure = sup {I = W (A ▷ B)} o

  -- This is trivially a closure ordinal.

  is-closure : (w : W (A ▷ B)) → o w < closure
  is-closure w = w , refl-≤

  -- It is also trivially the smallest such ordinal.

  is-minimal : ∀ {γ} → IsClosure γ → closure ≤ γ
  is-minimal cl w = cl w



-- -}
--
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
