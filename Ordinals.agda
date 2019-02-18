{-# OPTIONS --postfix-projections #-}

-- Plump ordinals following Mike Shulman's blog post.
-- See https://homotopytypetheory.org/2014/02/22/surreals-plump-ordinals/

open import Library

data Ord ℓ : Type (lsuc ℓ) where
  sup : ∀{I : Type ℓ} (f : I → Ord ℓ) → Ord ℓ

variable
  ℓ : Level
  α β γ : Ord ℓ
  I : Type ℓ
  i j : I
  f g : I → Ord ℓ

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

-- ∅ is left unit for ⊕

zero⊕-≤ : (∅ ⊕ β) ≤ β
zero⊕-≤ {β = sup g} (inj₁ ())
zero⊕-≤ {β = sup g} (inj₂ i) = i , zero⊕-≤ {β = g i}
-- zero⊕-≤ {β = sup g} = [ (λ()) , (λ i → i , zero⊕-≤ {β = g i}) ]

zero⊕-≥ : β ≤ (∅ ⊕ β)
zero⊕-≥ {β = sup g} i = inj₂ i , zero⊕-≥

zero⊕ : (∅ ⊕ β) ≅ β
zero⊕ = zero⊕-≤ , zero⊕-≥

-- ∅ is right unit for ⊕

⊕zero-≤ : (α ⊕ ∅) ≤ α
⊕zero-≤ {α = sup g} (inj₂ ())
⊕zero-≤ {α = sup g} (inj₁ i) = i , ⊕zero-≤ {α = g i}

⊕zero-≥ : α ≤ (α ⊕ ∅)
⊕zero-≥ {α = sup g} i = inj₁ i , ⊕zero-≥

⊕zero : (α ⊕ ∅) ≅ α
⊕zero = ⊕zero-≤ , ⊕zero-≥

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


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
