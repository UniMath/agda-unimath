# Unityped type theories

```agda
{-# OPTIONS --guardedness --allow-unsolved-metas #-}

module type-theories.unityped-type-theories where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

{{#concept "Unityped type theories"}} are type theories in which all terms have
the same type. They are sometimes called untyped type theories. The category of
unityped type theories is equivalent to the category of single sorted algebraic
theories.

## Definitions

```agda
module unityped where

  record system (l : Level) : UU (lsuc l)
    where
    coinductive
    field
      element : UU l
      slice : system l

  record system-Set (l : Level) : UU (lsuc l)
    where
    coinductive
    field
      element : Set l
      slice : system-Set l

  record hom-system
    {l1 l2 : Level} (σ : system l1) (T : system l2) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : system.element σ → system.element T
      slice : hom-system (system.slice σ) (system.slice T)

  id-hom-system :
    {l : Level} (σ : system l) → hom-system σ σ
  hom-system.element (id-hom-system σ) = id
  hom-system.slice (id-hom-system σ) = id-hom-system (system.slice σ)

  comp-hom-system :
    {l1 l2 l3 : Level} {σ : system l1} {τ : system l2} {υ : system l3}
    (β : hom-system τ υ) (α : hom-system σ τ) → hom-system σ υ
  hom-system.element (comp-hom-system β α) =
    hom-system.element β ∘ hom-system.element α
  hom-system.slice (comp-hom-system β α) =
    comp-hom-system (hom-system.slice β) (hom-system.slice α)

  record htpy-hom-system
    {l1 l2 : Level}
    {σ : system l1} {τ : system l2} (g h : hom-system σ τ) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : hom-system.element g ~ hom-system.element h
      slice : htpy-hom-system (hom-system.slice g) (hom-system.slice h)

  record weakening
    {l : Level} (σ : system l) : UU l
    where
    coinductive
    field
      element : hom-system σ (system.slice σ)
      slice : weakening (system.slice σ)

  record preserves-weakening
    {l1 l2 : Level}
    {σ : system l1} {τ : system l2}
    (Wσ : weakening σ) (Wτ : weakening τ)
    (h : hom-system σ τ) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element :
        htpy-hom-system
          ( comp-hom-system
            ( hom-system.slice h)
            ( weakening.element Wσ))
          ( comp-hom-system
            ( weakening.element Wτ)
            ( h))
      slice :
        preserves-weakening
          ( weakening.slice Wσ)
          ( weakening.slice Wτ)
          ( hom-system.slice h)

  record substitution
    {l : Level} (σ : system l) : UU l
    where
    coinductive
    field
      element :
        system.element σ → hom-system (system.slice σ) σ
      slice : substitution (system.slice σ)

  record preserves-substitution
    {l1 l2 : Level}
    {σ : system l1} {τ : system l2}
    (Sσ : substitution σ) (Sτ : substitution τ)
    (h : hom-system σ τ) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element :
        (x : system.element σ) →
        htpy-hom-system
          ( comp-hom-system
            ( h)
            ( substitution.element Sσ x))
          ( comp-hom-system
            ( substitution.element Sτ
              ( hom-system.element h x))
            ( hom-system.slice h))
      slice :
        preserves-substitution
          ( substitution.slice Sσ)
          ( substitution.slice Sτ)
          ( hom-system.slice h)

  record generic-element
    {l : Level} (σ : system l) : UU l
    where
    coinductive
    field
      element : system.element (system.slice σ)
      slice : generic-element (system.slice σ)

  record preserves-generic-element
    {l1 l2 : Level} {σ : system l1} {τ : system l2}
    (δσ : generic-element σ) (δτ : generic-element τ)
    (h : hom-system σ τ) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element :
        Id
          ( hom-system.element
            ( hom-system.slice h)
            ( generic-element.element δσ))
          ( generic-element.element δτ)
      slice :
        preserves-generic-element
          ( generic-element.slice δσ)
          ( generic-element.slice δτ)
          ( hom-system.slice h)

  record weakening-preserves-weakening
    {l : Level} {σ : system l} (W : weakening σ) : UU l
    where
    coinductive
    field
      element :
        preserves-weakening
          ( W)
          ( weakening.slice W)
          ( weakening.element W)
      slice :
        weakening-preserves-weakening (weakening.slice W)

  record substitution-preserves-substitution
    {l : Level} {σ : system l} (S : substitution σ) : UU l
    where
    coinductive
    field
      element :
        (x : system.element σ) →
        preserves-substitution
          ( substitution.slice S)
          ( S)
          ( substitution.element S x)
      slice :
        substitution-preserves-substitution (substitution.slice S)

  record weakening-preserves-substitution
    {l : Level} {σ : system l}
    (W : weakening σ) (S : substitution σ) : UU l
    where
    coinductive
    field
      element :
        preserves-substitution
          ( S)
          ( substitution.slice S)
          ( weakening.element W)
      slice :
        weakening-preserves-substitution
          ( weakening.slice W)
          ( substitution.slice S)

  record substitution-preserves-weakening
    {l : Level} {σ : system l} (W : weakening σ) (S : substitution σ) : UU l
    where
    coinductive
    field
      element :
        (x : system.element σ) →
        preserves-weakening
          ( weakening.slice W)
          ( W)
          ( substitution.element S x)
      slice :
        substitution-preserves-weakening
          ( weakening.slice W)
          ( substitution.slice S)

  record weakening-preserves-generic-element
    {l : Level} {σ : system l} (W : weakening σ) (δ : generic-element σ) : UU l
    where
    coinductive
    field
      element :
        preserves-generic-element
          ( δ)
          ( generic-element.slice δ)
          ( weakening.element W)
      slice :
        weakening-preserves-generic-element
          ( weakening.slice W)
          ( generic-element.slice δ)

  record substitution-preserves-generic-element
    {l : Level} {σ : system l} (S : substitution σ) (δ : generic-element σ) :
    UU l
    where
    coinductive
    field
      element :
        (x : system.element σ) →
        preserves-generic-element
          ( generic-element.slice δ)
          ( δ)
          ( substitution.element S x)
      slice :
        substitution-preserves-generic-element
          ( substitution.slice S)
          ( generic-element.slice δ)

  record substitution-cancels-weakening
    {l : Level} {σ : system l} (W : weakening σ) (S : substitution σ) : UU l
    where
    coinductive
    field
      element :
        (x : system.element σ) →
        htpy-hom-system
          ( comp-hom-system
            ( substitution.element S x)
            ( weakening.element W))
          ( id-hom-system σ)
      slice :
        substitution-cancels-weakening
          ( weakening.slice W)
          ( substitution.slice S)

  record generic-element-is-identity
    {l : Level} {σ : system l} (S : substitution σ) (δ : generic-element σ) :
    UU l
    where
    coinductive
    field
      element :
        (x : system.element σ) →
        hom-system.element
          ( substitution.element S x)
          ( generic-element.element δ) ＝
        x
      slice :
        generic-element-is-identity
          ( substitution.slice S)
          ( generic-element.slice δ)

  record substitution-by-generic-element
    {l : Level} {σ : system l} (W : weakening σ) (S : substitution σ)
    (δ : generic-element σ) : UU l
    where
    coinductive
    field
      element :
        htpy-hom-system
          ( comp-hom-system
            ( substitution.element
              ( substitution.slice S)
              ( generic-element.element δ))
            ( weakening.element (weakening.slice W)))
          ( id-hom-system (system.slice σ))
      slice :
        substitution-by-generic-element
          ( weakening.slice W)
          ( substitution.slice S)
          ( generic-element.slice δ)

  record type-theory
    (l : Level) : UU (lsuc l)
    where
    field
      sys : system l
      W : weakening sys
      S : substitution sys
      δ : generic-element sys
      WW : weakening-preserves-weakening W
      SS : substitution-preserves-substitution S
      WS : weakening-preserves-substitution W S
      SW : substitution-preserves-weakening W S
      Wδ : weakening-preserves-generic-element W δ
      Sδ : substitution-preserves-generic-element S δ
      S!W : substitution-cancels-weakening W S
      δid : generic-element-is-identity S δ
      Sδ! : substitution-by-generic-element W S δ

  slice-type-theory :
    {l : Level} (T : type-theory l) → type-theory l
  type-theory.sys (slice-type-theory T) =
    system.slice (type-theory.sys T)
  type-theory.W (slice-type-theory T) =
    weakening.slice (type-theory.W T)
  type-theory.S (slice-type-theory T) =
    substitution.slice (type-theory.S T)
  type-theory.δ (slice-type-theory T) =
    generic-element.slice (type-theory.δ T)
  type-theory.WW (slice-type-theory T) =
    weakening-preserves-weakening.slice (type-theory.WW T)
  type-theory.SS (slice-type-theory T) =
    substitution-preserves-substitution.slice (type-theory.SS T)
  type-theory.WS (slice-type-theory T) =
    weakening-preserves-substitution.slice (type-theory.WS T)
  type-theory.SW (slice-type-theory T) =
    substitution-preserves-weakening.slice (type-theory.SW T)
  type-theory.Wδ (slice-type-theory T) =
    weakening-preserves-generic-element.slice (type-theory.Wδ T)
  type-theory.Sδ (slice-type-theory T) =
    substitution-preserves-generic-element.slice (type-theory.Sδ T)
  type-theory.S!W (slice-type-theory T) =
    substitution-cancels-weakening.slice (type-theory.S!W T)
  type-theory.δid (slice-type-theory T) =
    generic-element-is-identity.slice (type-theory.δid T)
  type-theory.Sδ! (slice-type-theory T) =
    substitution-by-generic-element.slice (type-theory.Sδ! T)
```

---

```agda
  module C-system where

    El : {l : Level} (A : type-theory l) → ℕ → UU l
    El A zero-ℕ = system.element (type-theory.sys A)
    El A (succ-ℕ n) = El (slice-type-theory A) n

    iterated-weakening :
      {l : Level} {A : type-theory l} {m n : ℕ} →
      El A n → El A (succ-ℕ (m +ℕ n))
    iterated-weakening {l} {A} {zero-ℕ} {n} x =
      {!hom-system.element (weakening.element (type-theory.W A)) !}
    iterated-weakening {l} {A} {succ-ℕ m} {n} x = {!!}
```

`hom(X,Y) := Tm(W(X,Y))`

```agda
    hom : {l : Level} (A : type-theory l) → ℕ → ℕ → UU l
    hom A m n = El A (succ-ℕ (m +ℕ n))

    id-hom : {l : Level} (A : type-theory l) (n : ℕ) → hom A n n
    id-hom A zero-ℕ = generic-element.element (type-theory.δ A)
    id-hom A (succ-ℕ n) = {!!}
```

### The forgetful functor from unityped type theories to simple type theories

```agda
module simple-unityped where

{-
  system :
    {l : Level} → unityped.system l → simple.system l unit
  simple.system.element (system A) x = unityped.system.element A
  simple.system.slice (system A) x = system (unityped.system.slice A)

  hom-system :
    {l1 l2 : Level} {A : unityped.system l1} {B : unityped.system l2} →
    unityped.hom-system A B →
    simple.hom-system id
      ( system A)
      ( system B)
  simple.hom-system.element (hom-system f) = unityped.hom-system.element f
  simple.hom-system.slice (hom-system f) x =
    hom-system (unityped.hom-system.slice f)

  id-hom-system :
    {l : Level} (A : unityped.system l) →
    simple.htpy-hom-system
      ( hom-system (unityped.id-hom-system A))
      ( simple.id-hom-system (system A))
  simple.htpy-hom-system.element (id-hom-system A) x = refl-htpy
  simple.htpy-hom-system.slice (id-hom-system A) x =
    id-hom-system (unityped.system.slice A)

  comp-hom-system :
    {l1 l2 l3 : Level} {A : unityped.system l1} {B : unityped.system l2}
    {C : unityped.system l3} (g : unityped.hom-system B C)
    (f : unityped.hom-system A B) →
    simple.htpy-hom-system
      ( hom-system (unityped.comp-hom-system g f))
      ( simple.comp-hom-system
        ( hom-system g)
        ( hom-system f))
  simple.htpy-hom-system.element (comp-hom-system g f) x = refl-htpy
  simple.htpy-hom-system.slice (comp-hom-system g f) x =
    comp-hom-system
      ( unityped.hom-system.slice g)
      ( unityped.hom-system.slice f)

  htpy-hom-system :
    {l1 l2 : Level} {A : unityped.system l1} {B : unityped.system l2}
    {f g : unityped.hom-system A B} →
    unityped.htpy-hom-system f g →
    simple.htpy-hom-system (hom-system f) (hom-system g)
  simple.htpy-hom-system.element (htpy-hom-system H) x =
    unityped.htpy-hom-system.element H
  simple.htpy-hom-system.slice (htpy-hom-system H) x =
    htpy-hom-system (unityped.htpy-hom-system.slice H)

  weakening :
    {l : Level} {A : unityped.system l} → unityped.weakening A →
    simple.weakening (system A)
  simple.weakening.element (weakening W) x =
    hom-system (unityped.weakening.element W)
  simple.weakening.slice (weakening W) x =
    weakening (unityped.weakening.slice W)

  preserves-weakening :
    {l1 l2 : Level} {A : unityped.system l1} {B : unityped.system l2}
    {WA : unityped.weakening A} {WB : unityped.weakening B}
    {f : unityped.hom-system A B} →
    unityped.preserves-weakening WA WB f →
    simple.preserves-weakening (weakening WA) (weakening WB) (hom-system f)
  simple.preserves-weakening.element (preserves-weakening Wf) x =
    {!simple.concat-htpy-hom-system!}
  simple.preserves-weakening.slice (preserves-weakening Wf) = {!!}

  substitution :
    {l : Level} {A : unityped.system l} → unityped.substitution A →
    simple.substitution (system A)
  simple.substitution.element (substitution S) x =
    hom-system (unityped.substitution.element S x)
  simple.substitution.slice (substitution S) x =
    substitution (unityped.substitution.slice S)

  generic-element :
    {l : Level} {A : unityped.system l} → unityped.generic-element A →
    simple.generic-element (system A)
  simple.generic-element.element (generic-element δ) x =
    unityped.generic-element.element δ
  simple.generic-element.slice (generic-element δ) x =
    generic-element (unityped.generic-element.slice δ)
-}
```
