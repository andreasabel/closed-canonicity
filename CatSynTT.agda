{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --show-irrelevant #-}

-- Type theory with booleans

open import Level using (Level; _⊔_; Lift) renaming (zero to lzero; suc to lsuc)

open import Data.Bool.Base
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)

open import Function using (id; _on_)
open import Function.Bijection using (Bijective; Bijection; _∘_); open Bijection using (to; bijective; surjection); open Bijective using (injective; surjective)
open import Function.Surjection using (Surjective; Surjection); open Surjection using (from; from-to);  open Surjective using (right-inverse-of)
open import Function.Equality using (_⟶_; _⟨$⟩_; _⇨_)

open import Relation.Binary using (Setoid)
import Relation.Binary.On as On
import Relation.Binary.PropositionalEquality as PE
import Relation.Binary.EqReasoning as EqR

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
pattern euniv l = const (cuniv l)
pattern sid  = const cid
pattern eε = const cε
pattern π₁ = const cπ₁
pattern π₂ = const cπ₂
pattern ebit b = const (cbit b)
pattern arr a b = pi a (b ∙ π₁)

pattern 𝟙 = unit
pattern _^_ Γ a = sig Γ a

pattern inst b u = b ∙ pair sid u

-- Judgements

mutual

  -- Well-formed contexts

  -- data ⊢_ : (Γ : Exp) → Prop where

  -- Well typed terms

  data _⊢_∷_   : (Γ t a : Exp) → Prop where

    app : ∀{Γ a b t u : Exp}
      → (dt : Γ ⊢ t ∷ pi a b)
      → (du : Γ ⊢ u ∷ a)
      → Γ ⊢ app t u ∷ inst b u

    fst : ∀{Γ a b t : Exp}
      → (dt : Γ ⊢ t ∷ sig a b)
      → Γ ⊢ fst t ∷ a

    snd : ∀{Γ a b t : Exp}
      → (dt : Γ ⊢ t ∷ sig a b)
      → Γ ⊢ snd t ∷ inst b (fst t)

    ε : ∀{Γ}
      → Γ ⊢ eε ∷ 𝟙

    bit : ∀{Γ} b → Γ ⊢ ebit b ∷ bool

    ifthen : ∀{Γ l C c t e}
      → (dC : (Γ ^ bool) ⊢ C ∷ euniv l)
      → (dc : Γ ⊢ c ∷ bool)
      → (dt : Γ ⊢ t ∷ inst C (ebit true))
      → (de : Γ ⊢ e ∷ inst C (ebit false))
      → Γ ⊢ ifthen C c t e ∷ inst C c

    univ : ∀{Γ} {l} → Γ ⊢ euniv l ∷ euniv (1 + l)

    conv : ∀{Γ t a a' l}
      → (dt : Γ ⊢ t ∷ a)
      → (ea : Γ ⊢ a ≡ a' ∷ euniv l)
      → Γ ⊢ t ∷ a'

  -- Equal terms

  data _⊢_≡_∷_ : (Γ t t' a : Exp) → Prop where

    app : ∀{Γ a b t t' u u' : Exp}
      → (dt : Γ ⊢ t ≡ t' ∷ pi a b)
      → (du : Γ ⊢ u ≡ u' ∷ a)
      → Γ ⊢ app t u ≡ app t' u' ∷ inst b u

    bit : ∀{Γ} b → Γ ⊢ ebit b ≡ ebit b ∷ bool

    ε : ∀{Γ t t'}
      → (dt  : Γ ⊢ t ∷ 𝟙)
      → (dt' : Γ ⊢ t' ∷ 𝟙)
      → Γ ⊢ t ≡ t' ∷ 𝟙

    ifthen : ∀{Γ l C C' c c' t t' e e'}
      → (dC : (Γ ^ bool) ⊢ C ≡ C'  ∷ euniv l)
      → (dc : Γ ⊢ c ≡ c' ∷ bool)
      → (dt : Γ ⊢ t ≡ t' ∷ inst C (ebit true))
      → (de : Γ ⊢ e ≡ e' ∷ inst C (ebit false))
      → Γ ⊢ ifthen C c t e ≡ ifthen C' c' t' e' ∷ inst C c

    iftrue : ∀{Γ l C t e}
      → (dC : (Γ ^ bool) ⊢ C ∷ euniv l)
      → (dt : Γ ⊢ t ∷ inst C (ebit true))
      → (de : Γ ⊢ e ∷ inst C (ebit false))
      → Γ ⊢ ifthen C (ebit true) t e ≡ t ∷ inst C (ebit true)

    iffalse : ∀{Γ l C t e}
      → (dC : (Γ ^ bool) ⊢ C ∷ euniv l)
      → (dt : Γ ⊢ t ∷ inst C (ebit true))
      → (de : Γ ⊢ e ∷ inst C (ebit false))
      → Γ ⊢ ifthen C (ebit false) t e ≡ e ∷ inst C (ebit false)

    univ : ∀{Γ l} → Γ ⊢ euniv l ≡ euniv l ∷ euniv (1 + l)

    sym : ∀{Γ t u a}
      → (e  : Γ ⊢ t ≡ u ∷ a)
      → Γ ⊢ u ≡ t ∷ a

    trans : ∀{Γ a t u v}
      → (e  : Γ ⊢ t ≡ u ∷ a)
      → (e' : Γ ⊢ u ≡ v ∷ a)
      → Γ ⊢ t ≡ v ∷ a

    conv : ∀{Γ t t' a a' l}
      → (dt : Γ ⊢ t ≡ t' ∷ a)
      → (ea : Γ ⊢ a ≡ a' ∷ euniv l)
      → Γ ⊢ t ≡ t' ∷ a'

  -- Well-formed substitutions

  data _⊢ₛ_∷_   : (Γ s Δ : Exp) → Prop where

  -- Equal substitutions

  data _⊢ₛ_≡_∷_ : (Γ s s' Δ : Exp) → Prop where

-- Derived / admissible inferences

refl : ∀{Γ t a} (dt : Γ ⊢ t ∷ a) → Γ ⊢ t ≡ t ∷ a
refl = {!!}

inst-const : ∀{Γ t u a} (dt : Γ ⊢ t ∷ a) → Γ ⊢ (t ∙ eε) ∙ u ≡ t ∷ a
inst-const = {!!}

conv' : ∀{Γ t a a' l}
  → (dt : Γ ⊢ t ∷ a')
  → (ea : Γ ⊢ a ≡ a' ∷ euniv l)
  → Γ ⊢ t ∷ a
conv' dt ea = conv dt (sym ea)

conv'e : ∀{Γ t t' a a' l}
  → (dt : Γ ⊢ t ≡ t' ∷ a')
  → (ea : Γ ⊢ a ≡ a' ∷ euniv l)
  → Γ ⊢ t ≡ t' ∷ a
conv'e dt ea = conv dt (sym ea)

-- Closed terms

⊢₀_∷_ : (t a : Exp) → Prop
⊢₀ t ∷ a = 𝟙 ⊢ t ∷ a

⊢₀_≡_∷_ : (t t' a : Exp) → Prop
⊢₀ t ≡ t' ∷ a = 𝟙 ⊢ t ≡ t' ∷ a

-- Embedding ℕ into Agda's levels

level : (n : ℕ) → Level
level zero    = lzero
level (suc n) = lsuc (level n)

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

-- Interpretation of the universes

record Type l (a : Exp) : Set (level (1 + l)) where
  field
    -- Interpretation of term t
    intp : ∀ {t} (dt : ⊢₀ t ∷ a) → Setoid (level l) (level l)  -- Formal dependency on derivation dt

    -- J. equal terms have isomorphic interpretations
    bij  : ∀ {t t'}
      (dt : ⊢₀ t ∷ a)
      (dt' : ⊢₀ t' ∷ a)
      (ett' : ⊢₀ t ≡ t' ∷ a) →
      Bijection (intp dt) (intp dt')

    -- "K axiom" for identical terms
    -- The isomorphism between t and t is the identity isomorphim
    idc : ∀{t} (dt : ⊢₀ t ∷ a) (et : ⊢₀ t ≡ t ∷ a) (it : intp dt .Setoid.Carrier) → intp dt .Setoid._≈_ (bij dt dt et .to ⟨$⟩ it) it

    -- The bijections compose (pathes do not matter)
    coh :  ∀ {t₁ t₂ t₃}
      (dt₁ : ⊢₀ t₁ ∷ a)
      (dt₂ : ⊢₀ t₂ ∷ a)
      (dt₃ : ⊢₀ t₃ ∷ a)
      (et₁₂ : ⊢₀ t₁ ≡ t₂ ∷ a)
      (et₂₃ : ⊢₀ t₂ ≡ t₃ ∷ a)
      (et₁₃ : ⊢₀ t₁ ≡ t₃ ∷ a) →
      (bij dt₂ dt₃ et₂₃ ∘
       bij dt₁ dt₂ et₁₂) ≃
       bij dt₁ dt₃ et₁₃
      -- (it : intp dt₁ .Setoid.Carrier) →
      -- intp dt₃ .Setoid._≈_ (bij dt₂ dt₃ et₂₃ .to ⟨$⟩
      --                      (bij dt₁ dt₂ et₁₂ .to ⟨$⟩ it))
      --                      (bij dt₁ dt₃ et₁₃ .to ⟨$⟩ it)

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

typeEqRefl : ∀ {l a} (da : ⊢₀ a ∷ euniv l) (A : Type l a) → TypeEq A A
typeEqRefl {l} {a} da A .Bij {t} dta dtb = A .bij dta dtb (refl dta)
typeEqRefl {l} {a} da A .nat {t} {t'} dta dta' eta dtb dtb' etb = begin
    A .bij dta' dtb' (refl dta') ∘ A .bij dta dta' eta
  ≈⟨ A .coh dta dta' dtb' eta (refl dta') eta ⟩
    A .bij dta dtb' eta
  ≈⟨ S.sym {A .bij dtb dtb' etb ∘ A .bij dta dtb (refl dta)}
          {A .bij dta dtb' eta}
          (A .coh dta dtb dtb' (refl dta) etb eta) ⟩
    A .bij dtb dtb' etb ∘ A .bij dta dtb (refl dta)
  ∎
  where
  S = bijectionSetoid (A .intp dta) (A .intp dtb')
  module S = Setoid S
  open EqR S

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
    intp : ∀ {u} {du : ⊢₀ u ∷ a} (iu : Cand A du) → Type l (inst b u)
    bij  : ∀ {u u'}
      {du   : ⊢₀ u ∷ a}
      {du'  : ⊢₀ u' ∷ a}
      (euu' : ⊢₀ u ≡ u' ∷ a)
      {iu   : Cand A du}
      {iu'  : Cand A du'}
      (eiu  : CandHEq A du du' euu' iu iu')
      -- (let iu' = A .bij du du' euu' .to  ⟨$⟩ iu)
      {t} (dt : ⊢₀ t ∷ inst b u) (dt' : ⊢₀ t ∷ inst b u') →
      Bijection (intp iu .Type.intp dt) (intp iu' .Type.intp dt')
      -- We do not need to generalize this to ⊢₀ t ≡ t' ∷ a
      -- since we already have this in Type
    -- idc : ∀ {u}
    --   {du : ⊢₀ u ∷ a}
    --   (euu : ⊢₀ u ≡ u ∷ a)
    --   (iu  : Cand A du)
    --   (iu' : Cand A du)
    --   (φ   : CandHEq A du du euu iu iu')
    --   {t} (dt dt' : ⊢₀ t ∷ inst b u) (j : Cand (intp iu') dt) →
    --   intp iu' .Type.intp dt' .Setoid._≈_ (bij euu iu iu' φ dt dt' .to ⟨$⟩ j) j
    -- -- idc : ∀ {u}
    -- --   {du : ⊢₀ u ∷ a}
    -- --   (euu : ⊢₀ u ≡ u ∷ a)
    -- --   (iu  : Cand A du)
    -- --   (iu' : Cand A du)
    -- --   (φ   : CandHEq A du du euu iu iu')
    -- --   {t} (dt dt' : ⊢₀ t ∷ inst b u) (j : Cand (intp iu') dt) →
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
      (dt₁  : ⊢₀ t ∷ inst b u₁) (dt₁' : ⊢₀ t ∷ inst b' u₁)
      (dt₂  : ⊢₀ t ∷ inst b u₂) (dt₂' : ⊢₀ t ∷ inst b' u₂) →
      -- (φ : Bijection (Cand (B  .intp iu₁) dt) (Cand (B  .intp iu₂) dt')
      -- (ψ : Bijection (Cand (B' .intp iu₁) dt) (Cand (B' .intp iu₂) dt') →
      (TEq iu₂ .Bij dt₂ dt₂' ∘ B .bij eu₁₂ ei₁₂ dt₁ dt₂)
      ≃ (B' .bij eu₁₂ ei₁₂ dt₁' dt₂' ∘ TEq iu₁ .Bij dt₁ dt₁')

record FamEq {l a a'} {A : Type l a} {A' : Type l a'} (A=A' : TypeEq A A') {b b'} (B : Fam A b) (B' : Fam A' b') : Set (level l) where
  -- field
    -- Bij :

-- Unit type / empty context

record Unit {ℓ} : Set ℓ where
  constructor tt

⟦𝟙⟧ : ∀ l → Type l 𝟙
⟦𝟙⟧ l .intp ds .Setoid.Carrier = Unit
⟦𝟙⟧ l .intp ds .Setoid._≈_ _ _ = Unit
⟦𝟙⟧ l .intp ds .Setoid.isEquivalence .Relation.Binary.IsEquivalence.refl = _
⟦𝟙⟧ l .intp ds .Setoid.isEquivalence .Relation.Binary.IsEquivalence.sym _ = _
⟦𝟙⟧ l .intp ds .Setoid.isEquivalence .Relation.Binary.IsEquivalence.trans _ _ = _
⟦𝟙⟧ l .bij ds ds' ess' .to ._⟨$⟩_ _ = _
⟦𝟙⟧ l .bij ds ds' ess' .to .Function.Equality.cong _ = _
⟦𝟙⟧ l .bij ds ds' ess' .bijective .injective _ = _
⟦𝟙⟧ l .bij ds ds' ess' .bijective .surjective .Surjective.from = _
⟦𝟙⟧ l .bij ds ds' ess' .bijective .surjective .right-inverse-of _ = _
⟦𝟙⟧ l .idc d e i = _
⟦𝟙⟧ l .coh dt₁ dt₂ dt₃ et₁₂ et₂₃ et₁₃ it = _

⟦ε⟧ : ∀ l → Cand (⟦𝟙⟧ l) ε
⟦ε⟧ l = _

-- There should be a bijection A ≅ Fam 𝟙 (A ∙ ε)

raise : ∀{l a} (da : ⊢₀ a ∷ euniv l) (A : Type l a) → Fam (⟦𝟙⟧ l) (a ∙ eε)
raise {l} {a} da A .intp {u} {du} iu .intp {t} dt                          = A .intp (conv dt (inst-const da))
raise {l} {a} da A .intp {u} {du} iu .bij {t} {t'} dt dt' ett'             = A .bij  (conv dt (inst-const da)) (conv dt' (inst-const da)) (conv ett' (inst-const da))
raise {l} {a} da A .intp {u} {du} iu .idc {t} dt et it                     = A .idc (conv dt (inst-const da)) (conv et (inst-const da)) it
raise {l} {a} da A .bij {u} {u'} {du} {du'} euu' {iu} {iu'} eiu {t} dt dt' = A .bij  (conv dt (inst-const da)) (conv dt' (inst-const da)) (conv (refl dt) (inst-const da))
raise da A .intp iu .coh dt₁ dt₂ dt₃ et₁₂ et₂₃ et₁₃ it                          = A .coh (conv dt₁ (inst-const da)) (conv dt₂ (inst-const da)) (conv dt₃ (inst-const da)) (conv et₁₂ (inst-const da)) (conv et₂₃ (inst-const da)) (conv et₁₃ (inst-const da)) it

lower : ∀{l a} (da : ⊢₀ a ∷ euniv l) (F : Fam (⟦𝟙⟧ l) (a ∙ eε)) → Type l a
lower {l} {a} da F .intp {t} dt                   = F .intp {eε} {ε} (⟦ε⟧ l) .intp (conv' dt (inst-const da))
lower {l} {a} da F .bij {t} {t'} dt dt' ett'      = F .intp {eε} {ε} (⟦ε⟧ l) .bij  (conv' dt (inst-const da)) (conv' dt' (inst-const da)) (conv'e ett' (inst-const da))
lower {l} {a} da F .idc {t} dt et it              = F .intp {eε} {ε} (⟦ε⟧ l) .idc  (conv' dt (inst-const da)) (conv'e et (inst-const da)) it
lower {l} {a} da F .coh dt₁ dt₂ dt₃ et₁₂ et₂₃ et₁₃ it = F .intp {eε} {ε} (⟦ε⟧ l) .coh (conv' dt₁ (inst-const da)) (conv' dt₂ (inst-const da)) (conv' dt₃ (inst-const da)) (conv'e et₁₂ (inst-const da)) (conv'e et₂₃ (inst-const da)) (conv'e et₁₃ (inst-const da)) it

unitFam : ∀{l a} (da : ⊢₀ a ∷ euniv l) (A : Type l a) → TypeEq A (lower da (raise da A))
unitFam {l} {a} da A .Bij {t} dta dtb                        = A .bij _ _ _  -- dta (conv (conv' dtb (inst-const da)) (inst-const da)) (refl dta)
unitFam {l} {a} da A .nat {t} {t'} dta dta' eta dtb dtb' etb = typeEqRefl da A .nat _ _ _ _ _ _

famUnit : ∀{l a} (da : ⊢₀ a ∷ euniv l) (F : Fam (⟦𝟙⟧ l) (a ∙ eε)) → FamEq0 (⟦𝟙⟧ l) F (raise da (lower da F))
famUnit {l} {a} da F .FamEq0.TEq {u} {du} iu .Bij {t} dta dtb                               = F .bij (ε du ε) {iu} {⟦ε⟧ l} _ dta _
famUnit {l} {a} da F .FamEq0.TEq {u} {du} iu .nat {t} {t'} dta dta' eta dtb dtb'         = {!λ etb → ?!}
famUnit {l} {a} da F .FamEq0.nat {u₁} {u₂} {du₁} {du₂} eu₁₂ {iu₁} {iu₂} ei₁₂ {t} dt₁ dt₁' dt₂ dt₂' = {!!}

{-
-- Function type

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
⟦pi⟧ {a} A B .coh dt₁ dt₂ dt₃ et₁₂ et₂₃ et₁₃ = {!!}

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
⟦bool⟧ .intp {t} dt .Setoid.Carrier       = ∃ λ b → ⊢₀ t ≡ ebit b ∷ bool
⟦bool⟧ .intp {t} dt .Setoid._≈_           = PE._≡_ on proj₁
⟦bool⟧ .intp {t} dt .Setoid.isEquivalence = On.isEquivalence proj₁ PE.isEquivalence

⟦bool⟧ .bij dt dt' ett' .to ._⟨$⟩_ (b , eb)          = b , trans (sym ett') eb
⟦bool⟧ .bij dt dt' ett' .to .Function.Equality.cong = id
⟦bool⟧ .bij dt dt' ett' .bijective .injective       = id
⟦bool⟧ .bij dt dt' ett' .bijective .surjective .Surjective.from ._⟨$⟩_ (b , eb)          = b , trans ett' eb
⟦bool⟧ .bij dt dt' ett' .bijective .surjective .Surjective.from .Function.Equality.cong = id
⟦bool⟧ .bij dt dt' ett' .bijective .surjective .Surjective.right-inverse-of (b , eb)    = PE.refl

⟦bool⟧ .idc d e i = PE.refl
⟦bool⟧ .coh dt₁ dt₂ dt₃ et₁₂ et₂₃ et₁₃ PE.refl = PE.refl

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

-- Semantics of contexts

-- We have to restrict the level of the context, since we do not have Setω

data _⊢_ (l : ℕ) : (Γ : Exp) → Prop where

  cemp : l ⊢ 𝟙

  cext : ∀ {Γ a}
   (dΓ : l ⊢ Γ)
   (da : Γ ⊢ a ∷ euniv l)
   → l ⊢ (Γ ^ a)


-- Context extension

hcast : ∀ {l Γ} (G : Type l Γ) {b} (B : Fam G b) {σ} {ds : ⊢₀ σ ∷ Γ} (γ γ' : Cand G ds) (φ : CandEq G ds γ γ')
  {u} (du : ⊢₀ u ∷ inst b σ)
  → (i : Cand (B .intp γ) du)
  → Cand (B .intp γ') du
hcast {l} {Γ} G {b} B {σ} {ds} γ γ' φ du i =  B .bij (refl ds) {!!} du du .to ⟨$⟩ i

Sigma : ∀{l Γ} (G : Type l Γ) {b} (B : Fam G b) → Type l (Γ ^ b)
Sigma G B .intp dt .Setoid.Carrier               = ∃ λ (γ : Cand G (fst dt)) → Cand (B .intp γ) (snd dt)
Sigma G B .intp {σ} dt .Setoid._≈_ (γ , i) (γ' , i') = ∃ λ (φ : CandEq G (fst dt) γ γ') → CandEq (B .intp γ') (snd dt) (hcast G B γ γ' φ (snd dt) i) i'
Sigma {l} {Γ} G {b} B .intp {σ} dt .Setoid.isEquivalence .Relation.Binary.IsEquivalence.refl {γ , i} = Candrefl G (fst dt) γ , {!c!}
Sigma {l} {Γ} G {b} B .intp {σ} dt .Setoid.isEquivalence .Relation.Binary.IsEquivalence.sym = {!!}
Sigma {l} {Γ} G {b} B .intp {σ} dt .Setoid.isEquivalence .Relation.Binary.IsEquivalence.trans = {!!}
Sigma G B .bij  dt dt' ess' .to ._⟨$⟩_ = {!!}
Sigma G B .bij  dt dt' ess' .to .Function.Equality.cong = {!!}
Sigma G B .bij  dt dt' ess' .bijective .injective x₁ = {!!}
Sigma G B .bij  dt dt' ess' .bijective .surjective .Surjective.from ._⟨$⟩_ = {!!}
Sigma G B .bij  dt dt' ess' .bijective .surjective .Surjective.from .Function.Equality.cong = {!!}
Sigma G B .bij  dt dt' ess' .bijective .surjective .right-inverse-of (γ , i) = {!!}
Sigma G B .idc d e i = {!!}
Sigma _ _ .coh dt₁ dt₂ dt₃ et₁₂ et₂₃ et₁₃ = {!!}

-- Γ ⊧ t ∷ a

-- _⊧_∷_ : ∀{ℓ] (Γ t a : Exp) → Set


-- -}
-- -}
