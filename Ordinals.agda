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
  i : I
  f : I → Ord ℓ

mutual
  _<_ : (α β : Ord ℓ) → Type ℓ
  α < sup f = ∃ λ i → α ≤ f i

  _≤_ : (α β : Ord ℓ) → Type ℓ
  sup f ≤ β = ∀ i → f i < β

  _≅_ : (α β : Ord ℓ) → Type ℓ
  α ≅ β = (α ≤ β) × (β ≤ α)

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

-- Successor.

osuc : Ord ℓ → Ord ℓ
osuc α@(sup {I = I} f) = sup {I = Maybe I} (maybe f α)

osuc-< : α < osuc α
osuc-< {α = sup f} = nothing , refl-≤

-- If  α ≤ β  then  α < β+1.

osuc-≤-< : α ≤ β → α < osuc β
osuc-≤-< {β = sup g} p = nothing , p

-- If  α < β  then  α+1 ≤ β.

osuc-<-≤ : α < β → osuc α ≤ β
osuc-<-≤ {α = sup f} {β = sup g} (j , h) = maybe (λ i → (j , ≤-from-< (h i))) (j , h)

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
