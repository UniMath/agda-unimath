# Simplicially fully-faithful maps

```agda
module simplicial-type-theory.simplicially-fully-faithful-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types

open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.action-on-directed-edges-functions

```

</details>

## Idea

A ** simplicially fully-faithful map** from one type into another is a map that
induces [equivalences](foundation-core.equivalences.md) on
[hom-types](simplicial-type-theory.directed-edges.md). In other words, the
directed edges `f x →₂ f y` for a simplicially fully-faithful map `f : A → B`
are in one-to-one correspondence with the directed edges `x →₂ y`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-simplicially-fully-faithful : (A → B) → UU (l1 ⊔ l2)
  is-simplicially-fully-faithful f =
    (x y : A) → is-equiv (action-simplicial-hom-function f {x} {y})

  equiv-action-is-simplicially-fully-faithful :
    {f : A → B} (e : is-simplicially-fully-faithful f)
    {x y : A} → (x →₂ y) ≃ (f x →₂ f y)
  equiv-action-is-simplicially-fully-faithful {f} e {x} {y} =
    ( action-simplicial-hom-function f , e x y)

  inv-equiv-action-is-simplicially-fully-faithful :
    {f : A → B} (e : is-simplicially-fully-faithful f)
    {x y : A} → (f x →₂ f y) ≃ (x →₂ y)
  inv-equiv-action-is-simplicially-fully-faithful e =
    inv-equiv (equiv-action-is-simplicially-fully-faithful e)

infix 5 _↪▵_
_↪▵_ :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↪▵ B = Σ (A → B) (is-simplicially-fully-faithful)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-simplicially-fully-faithful-map : A ↪▵ B → A → B
  map-simplicially-fully-faithful-map = pr1

  is-simplicially-fully-faithful-map-simplicially-fully-faithful-map :
    (f : A ↪▵ B) →
    is-simplicially-fully-faithful (map-simplicially-fully-faithful-map f)
  is-simplicially-fully-faithful-map-simplicially-fully-faithful-map = pr2

  equiv-action-simplicially-fully-faithful-map :
    (e : A ↪▵ B) {x y : A} →
    ( x →₂ y) ≃
    ( map-simplicially-fully-faithful-map e x →₂
      map-simplicially-fully-faithful-map e y)
  equiv-action-simplicially-fully-faithful-map e =
    equiv-action-is-simplicially-fully-faithful
      ( is-simplicially-fully-faithful-map-simplicially-fully-faithful-map e)

  inv-equiv-action-simplicially-fully-faithful-map :
    (e : A ↪▵ B)
    {x y : A} →
    ( map-simplicially-fully-faithful-map e x →₂
      map-simplicially-fully-faithful-map e y) ≃
    ( x →₂ y)
  inv-equiv-action-simplicially-fully-faithful-map e =
    inv-equiv (equiv-action-simplicially-fully-faithful-map e)
```

## Examples

### The identity map is simplicially fully faithful

```agda
module _
  {l : Level} {A : UU l}
  where

  is-simplicially-fully-faithful-id :
    is-simplicially-fully-faithful (id {A = A})
  is-simplicially-fully-faithful-id x y =
    is-equiv-htpy id compute-action-simplicial-hom-id-function is-equiv-id

  id-simplicially-fully-faithful-map : A ↪▵ A
  pr1 id-simplicially-fully-faithful-map = id
  pr2 id-simplicially-fully-faithful-map = is-simplicially-fully-faithful-id
```

### To prove that a map is simplicially fully faithful, a point in the domain may be assumed

```agda
module _
  {l : Level} {A : UU l} {l2 : Level} {B : UU l2} {f : A → B}
  where

  abstract
    is-simplicially-fully-faithful-is-simplicially-fully-faithful :
      (A → is-simplicially-fully-faithful f) → is-simplicially-fully-faithful f
    is-simplicially-fully-faithful-is-simplicially-fully-faithful H x y =
      H x x y
```
