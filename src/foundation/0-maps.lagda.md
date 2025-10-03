# `0`-Maps

```agda
module foundation.0-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.sets
open import foundation-core.truncated-maps
open import foundation-core.truncation-levels
```

</details>

## Definition

Maps `f : A → B` of which the fibers are sets, i.e., 0-truncated types, are
called 0-maps. It is shown in
[`foundation.faithful-maps`](foundation.faithful-maps.md) that a map `f` is a
0-map if and only if `f` is faithful, i.e., `f` induces embeddings on identity
types.

```agda
module _
  {l1 l2 : Level}
  where

  is-0-map : {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
  is-0-map {A} {B} f = (y : B) → is-set (fiber f y)

  0-map : (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
  0-map A B = Σ (A → B) is-0-map

  map-0-map : {A : UU l1} {B : UU l2} → 0-map A B → A → B
  map-0-map = pr1

  is-0-map-0-map :
    {A : UU l1} {B : UU l2} (f : 0-map A B) → is-0-map (map-0-map f)
  is-0-map-0-map = pr2
```

## Properties

### Projections of families of sets are `0`-maps

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  abstract
    is-0-map-pr1 :
      {B : A → UU l2} → ((x : A) → is-set (B x)) → is-0-map (pr1 {B = B})
    is-0-map-pr1 {B} H x =
      is-set-equiv (B x) (equiv-fiber-pr1 B x) (H x)

  pr1-0-map :
    (B : A → Set l2) → 0-map (Σ A (λ x → type-Set (B x))) A
  pr1 (pr1-0-map B) = pr1
  pr2 (pr1-0-map B) = is-0-map-pr1 (λ x → is-set-type-Set (B x))
```

### `0`-maps are closed under homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  where

  is-0-map-htpy : is-0-map g → is-0-map f
  is-0-map-htpy = is-trunc-map-htpy zero-𝕋 H
```

### `0`-maps are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  is-0-map-comp :
    (g : B → X) (h : A → B) →
    is-0-map g → is-0-map h → is-0-map (g ∘ h)
  is-0-map-comp = is-trunc-map-comp zero-𝕋

  is-0-map-left-map-triangle :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-0-map g → is-0-map h → is-0-map f
  is-0-map-left-map-triangle = is-trunc-map-left-map-triangle zero-𝕋
```

### If a composite is a `0`-map, then so is its right factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  is-0-map-right-factor :
    (g : B → X) (h : A → B) →
    is-0-map g → is-0-map (g ∘ h) → is-0-map h
  is-0-map-right-factor = is-trunc-map-right-factor zero-𝕋

  is-0-map-top-map-triangle :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-0-map g → is-0-map f → is-0-map h
  is-0-map-top-map-triangle = is-trunc-map-top-map-triangle zero-𝕋
```

### Families of `0`-maps induce `0`-maps on total spaces

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-0-map-tot : ((x : A) → is-0-map (f x)) → is-0-map (tot f)
    is-0-map-tot = is-trunc-map-tot zero-𝕋
```

### For any type family over the codomain, a `0`-map induces a `0`-map on total spaces

In other words, `0`-maps are stable under pullbacks. We will come to this point
when we introduce homotopy pullbacks.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → B} (C : B → UU l3)
  where

  abstract
    is-0-map-Σ-map-base : is-0-map f → is-0-map (map-Σ-map-base f C)
    is-0-map-Σ-map-base = is-trunc-map-Σ-map-base zero-𝕋 C
```

### The functorial action of `Σ` preserves `0`-maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)}
  where

  is-0-map-Σ :
    is-0-map f → ((x : A) → is-0-map (g x)) → is-0-map (map-Σ D f g)
  is-0-map-Σ = is-trunc-map-Σ zero-𝕋 D
```
