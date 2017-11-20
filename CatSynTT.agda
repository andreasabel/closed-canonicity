{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --show-irrelevant #-}

-- Type theory with booleans

open import Level using (Level; _⊔_; Lift) renaming (zero to lzero; suc to lsuc)

open import Data.Bool.Base
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat.Base
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)

open import Function using (id; _on_)
open import Function.Bijection using (Bijective; Bijection; _∘_); open Bijection using (to; bijective; surjection); open Bijective using (injective; surjective)
open import Function.Surjection using (Surjective; Surjection); open Surjection using (from; from-to);  open Surjective using (right-inverse-of)
open import Function.Equality using (_⟶_; _⟨$⟩_; _⇨_)

open import Relation.Binary using (Setoid)
import Relation.Binary.On as On
import Relation.Binary.PropositionalEquality as PE

Prop = Set

-- Categorical syntax (explicit substitutions)

data Const : Set where
  -- Types
  cunit : Const
  cbool : Const
  cuniv : (l : ℕ) → Const
  -- Substitutions / terms
  cid : Const
  cε  : Const
  cπ₁ : Const
  -- Terms
  cπ₂ : Const
  cbit  : (b : Bool) → Const

data Exp : Set where
  -- Constants
  const : Const → Exp
  -- Types (b are binders)
  pi  : (a b : Exp) → Exp
  sig : (a b : Exp) → Exp
  -- Substitutions / terms
  _∙_ : (t s : Exp) → Exp  -- Composition
  pair : (u t : Exp) → Exp
  -- Terms
  fst snd : (t : Exp) → Exp  -- Needed?
  lam : (t : Exp) → Exp -- binder
  app : (t u : Exp) → Exp
  ifthen : (C c t e : Exp) → Exp  -- C is binder

pattern unit = const cunit
pattern bool = const cbool
pattern univ l = const (cuniv l)
pattern sid  = const cid
pattern ε = const cε
pattern π₁ = const cπ₁
pattern π₂ = const cπ₂
pattern bit b = const (cbit b)
pattern arr a b = pi a (b ∙ π₁)

pattern 𝟙 = unit

-- Judgements

mutual

  -- Well-formed contexts

  data ⊢_ : (Γ : Exp) → Prop where

  -- Well typed terms

  data _⊢_∷_[_]   : (Γ t a s : Exp) → Prop where

    app : ∀{Γ a b t u s : Exp}
      → (dt : Γ ⊢ t ∷ pi a b [ s ])
      → (du : Γ ⊢ u ∷ a [ s ])
      → Γ ⊢ app t u ∷ b [ pair s u ]

  -- Equal terms

  data _⊢_≡_∷_[_] : (Γ t t' a s : Exp) → Prop where

    app : ∀{Γ a b t t' u u' s : Exp}
      → (dt : Γ ⊢ t ≡ t' ∷ pi a b [ s ])
      → (du : Γ ⊢ u ≡ u' ∷ a [ s ])
      → Γ ⊢ app t u ≡ app t' u' ∷ b [ pair s u ]

    sym : ∀{Γ t u a s}
      → (e  : Γ ⊢ t ≡ u ∷ a [ s ])
      → Γ ⊢ u ≡ t ∷ a [ s ]

    trans : ∀{Γ a t u v s}
      → (e  : Γ ⊢ t ≡ u ∷ a [ s ])
      → (e' : Γ ⊢ u ≡ v ∷ a [ s ])
      → Γ ⊢ t ≡ v ∷ a [ s ]

  -- Well-formed substitutions

  data _⊢ₛ_∷_   : (Γ s Δ : Exp) → Prop where

  -- Equal substitutions

  data _⊢ₛ_≡_∷_ : (Γ s s' Δ : Exp) → Prop where

refl : ∀{Γ t a s} (dt : Γ ⊢ t ∷ a [ s ]) → Γ ⊢ t ≡ t ∷ a [ s ]
refl = {!!}

-- Closed terms

⊢₀_∷_ : (t a : Exp) → Prop
⊢₀ t ∷ a = 𝟙 ⊢ t ∷ a [ ε ]

⊢₀_≡_∷_ : (t t' a : Exp) → Prop
⊢₀ t ≡ t' ∷ a = 𝟙 ⊢ t ≡ t' ∷ a [ ε ]

-- Embedding ℕ into Agda's levels

level : (n : ℕ) → Level
level zero    = lzero
level (suc n) = lsuc (level n)

-- Interpretation of the universes

record Type l (a : Exp) : Set (level (1 + l)) where
  field
    intp : ∀ {t} (dt : ⊢₀ t ∷ a) → Setoid (level l) (level l)  -- Formal dependency on derivation dt
    bij  : ∀ {t t'}
      (dt : ⊢₀ t ∷ a)
      (dt' : ⊢₀ t' ∷ a)
      (ett' : ⊢₀ t ≡ t' ∷ a) →
      Bijection (intp dt) (intp dt')  -- This includes irrelevance of dt
      --  BUT NOT IRRELEVANCE OF ett' !!
    -- "K axiom" for identical terms
    idc : ∀{t} (d : ⊢₀ t ∷ a) (e : ⊢₀ t ≡ t ∷ a) (i : intp d .Setoid.Carrier) → intp d .Setoid._≈_ (bij d d e .to ⟨$⟩ i) i

open Type

-- Candidates

Cand : ∀{l a} (A : Type l a) {t} (d : ⊢₀ t ∷ a) → Set (level l)
Cand A d = A .intp d .Setoid.Carrier

CandEq : ∀{l a} (A : Type l a) {t} (d : ⊢₀ t ∷ a) (i j : Cand A d) → Set (level l)
CandEq A d i j = A .intp d .Setoid._≈_ i j

Candrefl : ∀{l a} (A : Type l a) {t} (d : ⊢₀ t ∷ a) (i : Cand A d) → CandEq A d i i
Candrefl A d i = A .intp d .Setoid.refl {i}

Candsym : ∀{l a} (A : Type l a) {t} (d : ⊢₀ t ∷ a) {i j : Cand A d} (eq : CandEq A d i j) → CandEq A d j i
Candsym A d eq = A .intp d .Setoid.sym eq

Candtrans : ∀{l a} (A : Type l a) {t} (d : ⊢₀ t ∷ a) {i j k : Cand A d} (eq : CandEq A d i j) (eq' : CandEq A d j k) → CandEq A d i k
Candtrans A d eq eq' = A .intp d .Setoid.trans eq eq'

cast : ∀{l a} (A : Type l a) {t t'} (dt : ⊢₀ t ∷ a) (dt' : ⊢₀ t' ∷ a)
  → (ett' : ⊢₀ t ≡ t' ∷ a)
  → (it : Cand A dt)
  → Cand A dt'
cast A dt dt' ett' it = A .bij dt dt' ett' .to ⟨$⟩ it

CandHEq : ∀{l a} (A : Type l a) {t t'} (dt : ⊢₀ t ∷ a) (dt' : ⊢₀ t' ∷ a) (ett' : ⊢₀ t ≡ t' ∷ a) (i : Cand A dt) (i' : Cand A dt') → Set (level l)
CandHEq A dt dt' ett' i i' = CandEq A dt' (cast A dt dt' ett' i) i'

castEq : ∀{l a} (A : Type l a) {t t'} (dt : ⊢₀ t ∷ a) (dt' : ⊢₀ t' ∷ a) (ett' : ⊢₀ t ≡ t' ∷ a) {i j : Cand A dt}
  → (eq : CandEq A dt i j)
  → CandEq A dt' (cast A dt dt' ett' i) (cast A dt dt' ett' j)
castEq A dt dt' ett' {i} {j} eq = A .bij dt dt' ett' .to .Function.Equality.cong eq

cast-inj : ∀{l a} (A : Type l a) {t t'} (dt : ⊢₀ t ∷ a) (dt' : ⊢₀ t' ∷ a) (ett' : ⊢₀ t ≡ t' ∷ a) {i j : Cand A dt}
  → (eq : CandEq A dt' (cast A dt dt' ett' i) (cast A dt dt' ett' j))
  → CandEq A dt i j
cast-inj A dt dt' ett' {i} {j} eq = A .bij dt dt' ett' .Bijection.injective eq

cast' : ∀{l a} (A : Type l a) {t t'} (dt : ⊢₀ t ∷ a) (dt' : ⊢₀ t' ∷ a)
  → (ett' : ⊢₀ t ≡ t' ∷ a)
  → (i : Cand A dt')
  → Cand A dt
cast' A dt dt' ett' i = from (surjection (A .bij dt dt' ett')) ⟨$⟩ i

cast'Eq : ∀{l a} (A : Type l a) {t t'} (dt : ⊢₀ t ∷ a) (dt' : ⊢₀ t' ∷ a) (ett' : ⊢₀ t ≡ t' ∷ a) {i j : Cand A dt'}
  → (eq : CandEq A dt' i j)
  → CandEq A dt (cast' A dt dt' ett' i) (cast' A dt dt' ett' j)
cast'Eq A dt dt' ett' {i} {j} eq = from (surjection (A .bij dt dt' ett')) .Function.Equality.cong eq

cast-cast' : ∀{l a} (A : Type l a) {t t'} (dt : ⊢₀ t ∷ a) (dt' : ⊢₀ t' ∷ a) (ett' : ⊢₀ t ≡ t' ∷ a) (i : Cand A dt')
  → CandEq A dt' (cast A dt dt' ett' (cast' A dt dt' ett' i)) i
cast-cast' A dt dt' ett' i = (A .bij dt dt' ett') .bijective .surjective .right-inverse-of i

-- Bijection equality

-- There is several equivalent ways to define bijection equality.
-- (f : A ≅ B : g) ≅ (f' : A ≅ B : g') holds iff
--  1. f ≈ f' : A ≅ B
--  2. g ≅ g' : B ≅ A
--  3. f : A ≅ B : g'
--  4. f' : A ≅ B : g

-- This could be in the standard library:

bijectionSetoid : ∀ {a a' b b'} (A : Setoid a a') (B : Setoid b b') → Setoid _ _
bijectionSetoid A B .Setoid.Carrier = Bijection A B
bijectionSetoid A B .Setoid._≈_ φ ψ = (A ⇨ B) .Setoid._≈_ (φ .to) (ψ .to)
bijectionSetoid A B .Setoid.isEquivalence = On.isEquivalence to ((A ⇨ B) .Setoid.isEquivalence)

BijectionEq : ∀ {a a' b b'} {A : Setoid a a'} {B : Setoid b b'} (φ ψ : Bijection A B) → Set _
BijectionEq {A = A} {B = B} φ ψ = bijectionSetoid A B .Setoid._≈_ φ ψ

_≃_ : ∀ {a a' b b'} {A : Setoid a a'} {B : Setoid b b'} (φ ψ : Bijection A B) → Set _
_≃_ = BijectionEq

-- Semantic type equality

record TypeEq {l a b} -- (da : ⊢₀ a ∷ univ l) (db : ⊢₀ b ∷ univ l) (e : ⊢₀ a ≡ b ∷ univ l)
              (A : Type l a) (B : Type l b) : Set (level l) where
  field
    Bij : ∀{t} (dta : ⊢₀ t ∷ a) (dtb : ⊢₀ t ∷ b) → Bijection (A .intp dta) (B .intp dtb)
    -- Naturality condition: Combining this bijection commutes with the bijections of A and B
    nat : ∀ {t t'}
      (dta  : ⊢₀ t  ∷ a)
      (dta' : ⊢₀ t' ∷ a)
      (eta  : ⊢₀ t ≡ t' ∷ a)
      (dtb  : ⊢₀ t  ∷ b)
      (dtb' : ⊢₀ t' ∷ b)
      (etb  : ⊢₀ t ≡ t' ∷ b) →
        (Bij dta' dtb' ∘ A .bij dta dta' eta)
        ≃ (B .bij dtb dtb' etb ∘ Bij dta dtb)
      -- (A .intp dta ⇨ B .intp dtb') .Setoid._≈_
      --   ((Bij dta' dtb' ∘ A .bij dta dta' eta) .to)
      --   ((B .bij dtb dtb' etb ∘ Bij dta dtb) .to)
open TypeEq

-- castCancel : ∀{l a} (A : Type l a) {t t'} (dt : ⊢₀ t ∷ a) (dt' : ⊢₀ t' ∷ a) (ett' : ⊢₀ t ≡ t' ∷ a) (et't : ⊢₀ t' ≡ t ∷ a) (i : Cand A dt')
--   → CandEq A dt' (cast A dt dt' ett' (cast A dt' dt et't i)) i
-- castCancel A dt dt' ett' et't i = {! (A .bij dt dt' ett') .bijective .surjective .right-inverse-of i!}  -- NOT TRUE, need to prove that cast only depends on t and t'
--  -- from-to (surjection (A .bij dt dt' ett')) {!!}

-- CandS : ∀{l a} (T : Type l a) → Setoid (level (1 + l)) (level (1 + l))
-- CandS {l} {a} T = Function.Equality.setoid (Term a)
--   record { Carrier       =  λ tdt → T .intp (proj₂ tdt) .Setoid.Carrier
--          ; _≈_           =  λ {tdt} {tdt'} e e' → {! T .intp (proj₂ tdt) .Setoid._≈_ !}
--          ; isEquivalence =  {! λ tdt → T .intp (proj₂ tdt) .Setoid.isEquivalence !}
--          }

-- Interpretation of the function space

record Fam {l a} (A : Type l a) (b : Exp) : Set (level (1 + l)) where
  field
    intp : ∀ {u} {du : ⊢₀ u ∷ a} (iu : Cand A du) → Type l (app b u)
    bij  : ∀ {u u'}
      {du   : ⊢₀ u ∷ a}
      {du'  : ⊢₀ u' ∷ a}
      (euu' : ⊢₀ u ≡ u' ∷ a)
      {iu   : Cand A du}
      {iu'  : Cand A du'}
      (eiu  : CandHEq A du du' euu' iu iu')
      -- (let iu' = A .bij du du' euu' .to  ⟨$⟩ iu)
      {t} (dt : ⊢₀ t ∷ app b u) (dt' : ⊢₀ t ∷ app b u') →
      Bijection (intp iu .Type.intp dt) (intp iu' .Type.intp dt')
      -- We do not need to generalize this to ⊢₀ t ≡ t' ∷ a
      -- since we already have this in Type
    -- idc : ∀ {u}
    --   {du : ⊢₀ u ∷ a}
    --   (euu : ⊢₀ u ≡ u ∷ a)
    --   (iu  : Cand A du)
    --   (iu' : Cand A du)
    --   (φ   : CandHEq A du du euu iu iu')
    --   {t} (dt dt' : ⊢₀ t ∷ app b u) (j : Cand (intp iu') dt) →
    --   intp iu' .Type.intp dt' .Setoid._≈_ (bij euu iu iu' φ dt dt' .to ⟨$⟩ j) j
    -- -- idc : ∀ {u}
    -- --   {du : ⊢₀ u ∷ a}
    -- --   (euu : ⊢₀ u ≡ u ∷ a)
    -- --   (iu  : Cand A du)
    -- --   (iu' : Cand A du)
    -- --   (φ   : CandHEq A du du euu iu iu')
    -- --   {t} (dt dt' : ⊢₀ t ∷ app b u) (j : Cand (intp iu') dt) →
    -- --   intp iu' .Type.intp dt' .Setoid._≈_ (bij euu iu iu' φ dt dt' .to ⟨$⟩ j) j
open Fam

-- Equal families over the same domain (warm-up)

record FamEq0 {l a} (A : Type l a) {b b'} (B : Fam A b) (B' : Fam A b') : Set (level l) where
  field
    TEq : ∀ {u} {du : ⊢₀ u ∷ a} (iu : Cand A du) → TypeEq (B .intp iu) (B' .intp iu)
    nat : ∀ {u₁ u₂}
      {du₁  : ⊢₀ u₁ ∷ a}
      {du₂  : ⊢₀ u₂ ∷ a}
      (eu₁₂ : ⊢₀ u₁ ≡ u₂ ∷ a)
      {iu₁  : Cand A du₁}
      {iu₂  : Cand A du₂}
      (ei₁₂ : CandHEq A du₁ du₂ eu₁₂ iu₁ iu₂) {t}
      (dt₁  : ⊢₀ t ∷ app b u₁) (dt₁' : ⊢₀ t ∷ app b' u₁)
      (dt₂  : ⊢₀ t ∷ app b u₂) (dt₂' : ⊢₀ t ∷ app b' u₂) →
      -- (φ : Bijection (Cand (B  .intp iu₁) dt) (Cand (B  .intp iu₂) dt')
      -- (ψ : Bijection (Cand (B' .intp iu₁) dt) (Cand (B' .intp iu₂) dt') →
      (TEq iu₂ .Bij dt₂ dt₂' ∘ B .bij eu₁₂ ei₁₂ dt₁ dt₂)
      ≃ (B' .bij eu₁₂ ei₁₂ dt₁' dt₂' ∘ TEq iu₁ .Bij dt₁ dt₁')

record FamEq {l a a'} {A : Type l a} {A' : Type l a'} (A=A' : TypeEq A A') {b b'} (B : Fam A b) (B' : Fam A' b') : Set (level l) where
  -- field
    -- Bij :

⟦pi⟧ : ∀{a b l} (A : Type l a) (B : Fam A b) → Type l (pi a b)
⟦pi⟧ {a} A B .intp {t} dt .Setoid.Carrier  = ∀ {u} {du : ⊢₀ u ∷ a} (iu : Cand A du) → Cand   (B .intp iu) (app dt du)
⟦pi⟧ {a} A B .intp {t} dt .Setoid._≈_ f f' = ∀ {u} {du : ⊢₀ u ∷ a} (iu : Cand A du) → CandEq (B .intp iu) (app dt du) (f iu) (f' iu)
⟦pi⟧ {a} A B .intp {t} dt .Setoid.isEquivalence .Relation.Binary.IsEquivalence.refl          {f} {u} {du} iu = Candrefl   (B .intp iu) (app dt du) (f  iu)
⟦pi⟧ {a} A B .intp {t} dt .Setoid.isEquivalence .Relation.Binary.IsEquivalence.sym           eq  {u} {du} iu = Candsym    (B .intp iu) (app dt du) (eq iu)
⟦pi⟧ {a} A B .intp {t} dt .Setoid.isEquivalence .Relation.Binary.IsEquivalence.trans      eq eq' {u} {du} iu = Candtrans  (B .intp iu) (app dt du) (eq iu) (eq' iu)
⟦pi⟧ {a} A B .bij dt dt' ett' .to ._⟨$⟩_                                                       f  {u} {du} iu = cast       (B .intp iu) (app dt du) (app dt' du) (app ett' (refl du)) (f  iu)
⟦pi⟧ {a} A B .bij dt dt' ett' .to .Function.Equality.cong                                     eq {u} {du} iu = castEq     (B .intp iu) (app dt du) (app dt' du) (app ett' (refl du)) (eq iu)
⟦pi⟧ {a} A B .bij dt dt' ett' .bijective .injective                                           eq {u} {du} iu = cast-inj   (B .intp iu) (app dt du) (app dt' du) (app ett' (refl du)) (eq iu)
⟦pi⟧ {a} A B .bij dt dt' ett' .bijective .surjective .Surjective.from ._⟨$⟩_                   f  {u} {du} iu = cast'      (B .intp iu) (app dt du) (app dt' du) (app ett' (refl du)) (f  iu)
⟦pi⟧ {a} A B .bij dt dt' ett' .bijective .surjective .Surjective.from .Function.Equality.cong eq {u} {du} iu = cast'Eq    (B .intp iu) (app dt du) (app dt' du) (app ett' (refl du)) (eq iu)
⟦pi⟧ {a} A B .bij dt dt' ett' .bijective .surjective .Surjective.right-inverse-of             f  {u} {du} iu = cast-cast' (B .intp iu) (app dt du) (app dt' du) (app ett' (refl du)) (f  iu)
⟦pi⟧ {a} A B .idc dt ett                                                                      f  {u} {du} iu = B .intp iu .idc (app dt du) (app ett (refl du)) (f iu)

⟦fun≡fun⟧ : ∀ {a b l} {A : Type l a} {B : Fam A b} {a' b'} {A' : Type l a'} {B' : Fam A' b'} (A=A' : TypeEq A A') (B=B' : FamEq A=A' B B') → TypeEq (⟦pi⟧ A B) (⟦pi⟧ A' B')
⟦fun≡fun⟧ = {!!}

-- Interpretation of application is just application of the meta-theory

⟦app⟧ : ∀{a b l} {A : Type l a} {B : Fam A b} {t u}
  (dt : ⊢₀ t ∷ pi a b) (it : Cand (⟦pi⟧ A B) dt) →
  (du : ⊢₀ u ∷ a      ) (iu : Cand A du) →
  Cand (B .intp iu) (app dt du)
⟦app⟧ dt it du iu = it iu

-- Interpretation of type bool

⟦bool⟧ : Type 0 bool
⟦bool⟧ .intp {t} dt .Setoid.Carrier       = ∃ λ b → ⊢₀ t ≡ bit b ∷ bool
⟦bool⟧ .intp {t} dt .Setoid._≈_           = PE._≡_ on proj₁
⟦bool⟧ .intp {t} dt .Setoid.isEquivalence = On.isEquivalence proj₁ PE.isEquivalence

⟦bool⟧ .bij dt dt' ett' .to ._⟨$⟩_ (b , eb)          = b , trans (sym ett') eb
⟦bool⟧ .bij dt dt' ett' .to .Function.Equality.cong = id
⟦bool⟧ .bij dt dt' ett' .bijective .injective       = id
⟦bool⟧ .bij dt dt' ett' .bijective .surjective .Surjective.from ._⟨$⟩_ (b , eb)          = b , trans ett' eb
⟦bool⟧ .bij dt dt' ett' .bijective .surjective .Surjective.from .Function.Equality.cong = id
⟦bool⟧ .bij dt dt' ett' .bijective .surjective .Surjective.right-inverse-of (b , eb)    = PE.refl

⟦bool⟧ .idc d e i = PE.refl

-- Equality of type bool to itself
⟦bool≡bool⟧ : TypeEq ⟦bool⟧ ⟦bool⟧
⟦bool≡bool⟧ .TypeEq.Bij dta dtb = Function.Bijection.id
⟦bool≡bool⟧ .TypeEq.nat dta dta' eta dtb dtb' etb = id
-- ⟦bool≡bool⟧ .TypeEq.Bij dta dtb .to ._⟨$⟩_ (b , db) = b , db
-- ⟦bool≡bool⟧ .TypeEq.Bij {t} dta dtb .to .Function.Equality.cong {b , db} {b' , db'} eq = eq
-- ⟦bool≡bool⟧ .TypeEq.Bij dta dtb .bijective .injective {b , db} {b' , db'} eq = eq
-- ⟦bool≡bool⟧ .TypeEq.Bij dta dtb .bijective .surjective .Surjective.from ._⟨$⟩_ (b , db) = b , db
-- ⟦bool≡bool⟧ .TypeEq.Bij dta dtb .bijective .surjective .Surjective.from .Function.Equality.cong eq = eq
-- ⟦bool≡bool⟧ .TypeEq.Bij dta dtb .bijective .surjective .right-inverse-of (b , db) = PE.refl
-- ⟦bool≡bool⟧ .TypeEq.nat dta dta' eta dtb dtb' etb {b , db} {b' , db'} eq = eq

-- Interpretation of bits

⟦bit⟧ : ∀ b → Cand ⟦bool⟧ (bit b)
⟦bit⟧ b = b , bit b
{-
-- Semantics of contexts

-- We have to restrict the level of the context, since we do not have Setω

data _⊢_ (l : ℕ) : ∀ {n} (Γ : Cxt n) → Prop where

  ε    : l ⊢ ε

  cext : ∀{n}{Γ : Cxt n} {a : Exp n}
   (dΓ : l ⊢ Γ)
   (da : Γ ⊢ a ∷ univ l)
   → l ⊢ (Γ , a)

-- Interpretation of contexts

record Con l {n} (Γ : Cxt n) : Set (level (1 + l)) where
  field
    intp : ∀ {σ} (ds : ⊢₀ₛ σ ∷ Γ) → Setoid (level l) (level l)  -- Formal dependency on derivation dt
    bij  : ∀ {σ σ'}
      (ds : ⊢₀ₛ σ ∷ Γ)
      (ds' : ⊢₀ₛ σ' ∷ Γ)
      (ess' : ⊢₀ₛ σ ≡ σ' ∷ Γ) →
      Bijection (intp ds) (intp ds')
open Con

-- Context candidates

Cond : ∀{l n} {Γ : Cxt n} (G : Con l Γ) {σ} (d : ⊢₀ₛ σ ∷ Γ) → Set (level l)
Cond G d = G .intp d .Setoid.Carrier

CondEq : ∀{l n} {Γ : Cxt n} (G : Con l Γ) {σ} (d : ⊢₀ₛ σ ∷ Γ) (i j : Cond G d) → Set (level l)
CondEq G d i j = G .intp d .Setoid._≈_ i j

Condrefl : ∀{l n} {Γ : Cxt n} (G : Con l Γ) {σ} (d : ⊢₀ₛ σ ∷ Γ) (i : Cond G d) → CondEq G d i i
Condrefl G d i = G .intp d .Setoid.refl {i}

Condsym : ∀{l n} {Γ : Cxt n} (G : Con l Γ) {σ} (d : ⊢₀ₛ σ ∷ Γ) {i j : Cond G d} (eq : CondEq G d i j) → CondEq G d j i
Condsym G d eq = G .intp d .Setoid.sym eq

Condtrans : ∀{l n} {Γ : Cxt n} (G : Con l Γ) {σ} (d : ⊢₀ₛ σ ∷ Γ) {i j k : Cond G d} (eq : CondEq G d i j) (eq' : CondEq G d j k) → CondEq G d i k
Condtrans G d eq eq' = G .intp d .Setoid.trans eq eq'

cost : ∀{l n} {Γ : Cxt n} (G : Con l Γ) {σ σ'} (dσ : ⊢₀ₛ σ ∷ Γ) (dσ' : ⊢₀ₛ σ' ∷ Γ) (eσσ' : ⊢₀ₛ σ ≡ σ' ∷ Γ) (γ : Cond G dσ) →  Cond G dσ'
cost G d d' e γ = G .bij d d' e .to ⟨$⟩ γ

CondHEq : ∀{l n} {Γ : Cxt n} (G : Con l Γ) {σ σ'} (dσ : ⊢₀ₛ σ ∷ Γ) (dσ' : ⊢₀ₛ σ' ∷ Γ) (eσσ' : ⊢₀ₛ σ ≡ σ' ∷ Γ) (γ : Cond G dσ) (γ' : Cond G dσ') → Set (level l)
CondHEq G dσ dσ' eσσ' γ γ' = CondEq G dσ' (cost G dσ dσ' eσσ' γ) γ'

condHEq : ∀{l n} {Γ : Cxt n} (G : Con l Γ) {σ} (d : ⊢₀ₛ σ ∷ Γ) (γ γ' : Cond G d) (eq : CondEq G d γ γ') → CondHEq G d d (reflₛ Γ d) γ γ'
condHEq {l} {n} {Γ} G {σ} d γ γ' eq = {!!}



-- Empty context

⟦ε⟧ : ∀{l} → Con l ε
⟦ε⟧ .intp ds .Setoid.Carrier = Lift ⊤
⟦ε⟧ .intp ds .Setoid._≈_ _ _ = Lift ⊤
⟦ε⟧ .intp ds .Setoid.isEquivalence .Relation.Binary.IsEquivalence.refl = _
⟦ε⟧ .intp ds .Setoid.isEquivalence .Relation.Binary.IsEquivalence.sym _ = _
⟦ε⟧ .intp ds .Setoid.isEquivalence .Relation.Binary.IsEquivalence.trans _ _ = _
⟦ε⟧ .bij ds ds' ess' .to ._⟨$⟩_ _ = _
⟦ε⟧ .bij ds ds' ess' .to .Function.Equality.cong _ = _
⟦ε⟧ .bij ds ds' ess' .bijective .injective _ = _
⟦ε⟧ .bij ds ds' ess' .bijective .surjective .Surjective.from = _
⟦ε⟧ .bij ds ds' ess' .bijective .surjective .right-inverse-of _ = _

-- Context extension

record SFam {l n} {Γ : Cxt n} (G : Con l Γ) (b : Exp n) : Set (level (1 + l)) where
  field
    intp : ∀ {σ} {ds : ⊢₀ₛ σ ∷ Γ} (γ : Cond G ds) → Type l (sub σ b)
    bij  : ∀ {σ σ'}
      {ds : ⊢₀ₛ σ ∷ Γ}
      {ds' : ⊢₀ₛ σ' ∷ Γ}
      (ess' : ⊢₀ₛ σ ≡ σ' ∷ Γ)
      (γ : Cond G ds)
      (γ' : Cond G ds')
      (h : CondHEq G ds ds' ess' γ γ')
      -- Need heterogenous equality!
      -- (let γ' = G .bij ds ds' ess' .to  ⟨$⟩ γ)
      {t} (dt : ⊢₀ t ∷ sub σ b) (dt' : ⊢₀ t ∷ sub σ' b) →
      Bijection (intp γ .Type.intp dt) (intp γ' .Type.intp dt')
      -- We do not need to generalize this to ⊢₀ t ≡ t' ∷ Γ
      -- since we already have this in Type
open SFam

hcast : ∀ {l n} {Γ : Cxt n} (G : Con l Γ) {b} (B : SFam G b) {σ} {ds : ⊢₀ₛ σ ∷ Γ} (γ γ' : Cond G ds) (φ : CondEq G ds γ γ')
  {u} (du : ⊢₀ u ∷ sub σ b)
  → (i : Cand (B .intp γ) du)
  → Cand (B .intp γ') du
hcast {l} {n} {Γ} G {b} B {σ} {ds} γ γ' φ du i = B .bij (reflₛ Γ ds) γ γ' {!!} du du .to ⟨$⟩ i


Sigma : ∀{l n} {Γ : Cxt n} (G : Con l Γ) {b : Exp n} (B : SFam G b) → Con l (Γ , b)
Sigma G B .intp (ds , du) .Setoid.Carrier               = ∃ λ (γ : Cond G ds) → Cand (B .intp γ) du
Sigma G B .intp {σ} (ds , du) .Setoid._≈_ (γ , i) (γ' , i') = ∃ λ (φ : CondEq G ds γ γ') → CandEq (B .intp γ') du (hcast G B γ γ' φ du i) i'
Sigma {l} {n} {Γ} G {b} B .intp {σ} (ds , du) .Setoid.isEquivalence .Relation.Binary.IsEquivalence.refl {γ , i} = Condrefl G ds γ , {!!}
Sigma {l} {n} {Γ} G {b} B .intp {σ} (ds , du) .Setoid.isEquivalence .Relation.Binary.IsEquivalence.sym = {!!}
Sigma {l} {n} {Γ} G {b} B .intp {σ} (ds , du) .Setoid.isEquivalence .Relation.Binary.IsEquivalence.trans = {!!}
Sigma G B .bij  (ds , du) (ds' , du') ess' .to ._⟨$⟩_ = {!!}
Sigma G B .bij  (ds , du) (ds' , du') ess' .to .Function.Equality.cong = {!!}
Sigma G B .bij  (ds , du) (ds' , du') ess' .bijective .injective x₁ = {!!}
Sigma G B .bij  (ds , du) (ds' , du') ess' .bijective .surjective .Surjective.from ._⟨$⟩_ = {!!}
Sigma G B .bij  (ds , du) (ds' , du') ess' .bijective .surjective .Surjective.from .Function.Equality.cong = {!!}
Sigma G B .bij  (ds , du) (ds' , du') ess' .bijective .surjective .right-inverse-of (γ , i) = {!!}

-- Con : ∀{l n} {Γ : Cxt n} (dΓ : l ⊢ Γ) → Set (level (1 + l))
-- Con ε = {!!}
-- Con (cext dΓ da) = {!!}


-- -}
-- -}
