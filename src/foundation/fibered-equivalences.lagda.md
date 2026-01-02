# Fibered equivalences

```agda
module foundation.fibered-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.equivalences-slice
open import foundation.fibered-maps
open import foundation.logical-equivalences
open import foundation.pullbacks
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.families-of-equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Idea

A fibered equivalence is a fibered map

```text
       h
  A -------> B
  |          |
 f|          |g
  |          |
  ∨          ∨
  X -------> Y
       i
```

such that both `i` and `h` are equivalences.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  equiv-over : (X → Y) → UU (l1 ⊔ l2 ⊔ l4)
  equiv-over i = Σ (A ≃ B) (is-map-over f g i ∘ map-equiv)

  fibered-equiv : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fibered-equiv = Σ (X ≃ Y) (equiv-over ∘ map-equiv)

  fiberwise-equiv-over : (X → Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fiberwise-equiv-over i =
    Σ (fiberwise-map-over f g i) is-fiberwise-equiv

  fam-equiv-over : (X → Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fam-equiv-over i = (x : X) → (fiber f x) ≃ (fiber g (i x))
```

## Properties

### The induced maps on fibers are equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (i : X → Y)
  where

  eq-equiv-over-equiv-slice : equiv-slice (i ∘ f) g ＝ equiv-over f g i
  eq-equiv-over-equiv-slice = refl

  eq-equiv-slice-equiv-over : equiv-over f g i ＝ equiv-slice (i ∘ f) g
  eq-equiv-slice-equiv-over = refl

  equiv-equiv-over-fiberwise-equiv :
    fiberwise-equiv (fiber (i ∘ f)) (fiber g) ≃ equiv-over f g i
  equiv-equiv-over-fiberwise-equiv =
    equiv-equiv-slice-fiberwise-equiv (i ∘ f) g
```

### Fibered equivalences embed into the type of fibered maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (i : X → Y)
  where

  map-Σ-is-equiv-equiv-over :
    (equiv-over f g i) → Σ (map-over f g i) (is-equiv ∘ pr1)
  pr1 (pr1 (map-Σ-is-equiv-equiv-over ((h , is-equiv-h) , H))) = h
  pr2 (pr1 (map-Σ-is-equiv-equiv-over ((h , is-equiv-h) , H))) = H
  pr2 (map-Σ-is-equiv-equiv-over ((h , is-equiv-h) , H)) = is-equiv-h

  map-equiv-over-Σ-is-equiv :
    Σ (map-over f g i) (is-equiv ∘ pr1) → (equiv-over f g i)
  pr1 (pr1 (map-equiv-over-Σ-is-equiv ((h , H) , is-equiv-h))) = h
  pr2 (pr1 (map-equiv-over-Σ-is-equiv ((h , H) , is-equiv-h))) = is-equiv-h
  pr2 (map-equiv-over-Σ-is-equiv ((h , H) , is-equiv-h)) = H

  is-equiv-map-Σ-is-equiv-equiv-over : is-equiv map-Σ-is-equiv-equiv-over
  is-equiv-map-Σ-is-equiv-equiv-over =
    is-equiv-is-invertible map-equiv-over-Σ-is-equiv refl-htpy refl-htpy

  equiv-Σ-is-equiv-equiv-over :
    (equiv-over f g i) ≃ Σ (map-over f g i) (is-equiv ∘ pr1)
  pr1 equiv-Σ-is-equiv-equiv-over = map-Σ-is-equiv-equiv-over
  pr2 equiv-Σ-is-equiv-equiv-over = is-equiv-map-Σ-is-equiv-equiv-over

  is-equiv-map-equiv-over-Σ-is-equiv : is-equiv map-equiv-over-Σ-is-equiv
  is-equiv-map-equiv-over-Σ-is-equiv =
    is-equiv-is-invertible map-Σ-is-equiv-equiv-over refl-htpy refl-htpy

  equiv-equiv-over-Σ-is-equiv :
    Σ (map-over f g i) (is-equiv ∘ pr1) ≃ (equiv-over f g i)
  pr1 equiv-equiv-over-Σ-is-equiv = map-equiv-over-Σ-is-equiv
  pr2 equiv-equiv-over-Σ-is-equiv = is-equiv-map-equiv-over-Σ-is-equiv

  emb-map-over-equiv-over : equiv-over f g i ↪ map-over f g i
  emb-map-over-equiv-over =
    comp-emb
      ( emb-subtype (is-equiv-Prop ∘ pr1))
      ( emb-equiv equiv-Σ-is-equiv-equiv-over)

  map-over-equiv-over : equiv-over f g i → map-over f g i
  map-over-equiv-over = map-emb emb-map-over-equiv-over

  is-emb-map-over-equiv-over : is-emb map-over-equiv-over
  is-emb-map-over-equiv-over = is-emb-map-emb emb-map-over-equiv-over

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  is-fibered-equiv-fibered-map : fibered-map f g → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-fibered-equiv-fibered-map (i , h , H) = is-equiv i × is-equiv h

  map-Σ-is-fibered-equiv-fibered-map-fibered-equiv :
    (fibered-equiv f g) → Σ (fibered-map f g) (is-fibered-equiv-fibered-map)
  pr1 (pr1 (map-Σ-is-fibered-equiv-fibered-map-fibered-equiv
    ((i , is-equiv-i) , (h , is-equiv-h) , H))) = i
  pr1 (pr2 (pr1 (map-Σ-is-fibered-equiv-fibered-map-fibered-equiv
    ((i , is-equiv-i) , (h , is-equiv-h) , H)))) = h
  pr2 (pr2 (pr1 (map-Σ-is-fibered-equiv-fibered-map-fibered-equiv
    ((i , is-equiv-i) , (h , is-equiv-h) , H)))) = H
  pr1 (pr2 (map-Σ-is-fibered-equiv-fibered-map-fibered-equiv
    ((i , is-equiv-i) , (h , is-equiv-h) , H))) = is-equiv-i
  pr2 (pr2 (map-Σ-is-fibered-equiv-fibered-map-fibered-equiv
    ((i , is-equiv-i) , (h , is-equiv-h) , H))) = is-equiv-h

  map-fibered-equiv-Σ-is-fibered-equiv-fibered-map :
    (Σ (fibered-map f g) (is-fibered-equiv-fibered-map)) → (fibered-equiv f g)
  pr1 (pr1 (map-fibered-equiv-Σ-is-fibered-equiv-fibered-map
    ((i , h , H) , is-equiv-i , is-equiv-h))) = i
  pr2 (pr1 (map-fibered-equiv-Σ-is-fibered-equiv-fibered-map
    ((i , h , H) , is-equiv-i , is-equiv-h))) = is-equiv-i
  pr1 (pr1 (pr2 (map-fibered-equiv-Σ-is-fibered-equiv-fibered-map
    ((i , h , H) , is-equiv-i , is-equiv-h)))) = h
  pr2 (pr1 (pr2 (map-fibered-equiv-Σ-is-fibered-equiv-fibered-map
    ((i , h , H) , is-equiv-i , is-equiv-h)))) = is-equiv-h
  pr2 (pr2 (map-fibered-equiv-Σ-is-fibered-equiv-fibered-map
    ((i , h , H) , is-equiv-i , is-equiv-h))) = H

  is-equiv-map-Σ-is-fibered-equiv-fibered-map-fibered-equiv :
    is-equiv (map-Σ-is-fibered-equiv-fibered-map-fibered-equiv)
  is-equiv-map-Σ-is-fibered-equiv-fibered-map-fibered-equiv =
    is-equiv-is-invertible
      ( map-fibered-equiv-Σ-is-fibered-equiv-fibered-map)
      ( refl-htpy)
      ( refl-htpy)

  equiv-Σ-is-fibered-equiv-fibered-map-fibered-equiv :
    (fibered-equiv f g) ≃ Σ (fibered-map f g) (is-fibered-equiv-fibered-map)
  pr1 equiv-Σ-is-fibered-equiv-fibered-map-fibered-equiv =
    map-Σ-is-fibered-equiv-fibered-map-fibered-equiv
  pr2 equiv-Σ-is-fibered-equiv-fibered-map-fibered-equiv =
    is-equiv-map-Σ-is-fibered-equiv-fibered-map-fibered-equiv

  is-equiv-map-fibered-equiv-Σ-is-fibered-equiv-fibered-map :
    is-equiv (map-fibered-equiv-Σ-is-fibered-equiv-fibered-map)
  is-equiv-map-fibered-equiv-Σ-is-fibered-equiv-fibered-map =
    is-equiv-is-invertible
      ( map-Σ-is-fibered-equiv-fibered-map-fibered-equiv)
      ( refl-htpy)
      ( refl-htpy)

  equiv-fibered-equiv-Σ-is-fibered-equiv-fibered-map :
    Σ (fibered-map f g) (is-fibered-equiv-fibered-map) ≃ (fibered-equiv f g)
  pr1 equiv-fibered-equiv-Σ-is-fibered-equiv-fibered-map =
    map-fibered-equiv-Σ-is-fibered-equiv-fibered-map
  pr2 equiv-fibered-equiv-Σ-is-fibered-equiv-fibered-map =
    is-equiv-map-fibered-equiv-Σ-is-fibered-equiv-fibered-map

  is-prop-is-fibered-equiv-fibered-map :
    (ihH : fibered-map f g) → is-prop (is-fibered-equiv-fibered-map ihH)
  is-prop-is-fibered-equiv-fibered-map (i , h , H) =
    is-prop-product (is-property-is-equiv i) (is-property-is-equiv h)

  is-fibered-equiv-fibered-map-Prop :
    fibered-map f g → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 (is-fibered-equiv-fibered-map-Prop ihH) =
    is-fibered-equiv-fibered-map ihH
  pr2 (is-fibered-equiv-fibered-map-Prop ihH) =
    is-prop-is-fibered-equiv-fibered-map ihH

  emb-fibered-map-fibered-equiv : fibered-equiv f g ↪ fibered-map f g
  emb-fibered-map-fibered-equiv =
    comp-emb
      ( emb-subtype is-fibered-equiv-fibered-map-Prop)
      ( emb-equiv equiv-Σ-is-fibered-equiv-fibered-map-fibered-equiv)

  fibered-map-fibered-equiv : fibered-equiv f g → fibered-map f g
  fibered-map-fibered-equiv = map-emb emb-fibered-map-fibered-equiv

  is-emb-fibered-map-fibered-equiv : is-emb fibered-map-fibered-equiv
  is-emb-fibered-map-fibered-equiv =
    is-emb-map-emb emb-fibered-map-fibered-equiv
```

### Extensionality for equivalences over

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (i : X → Y)
  where

  extensionality-equiv-over :
    (e e' : equiv-over f g i) →
    ( e ＝ e') ≃
    ( htpy-map-over f g i
      ( map-over-equiv-over f g i e)
      ( map-over-equiv-over f g i e'))
  extensionality-equiv-over e e' =
    ( extensionality-map-over f g i
      ( map-over-equiv-over f g i e)
      ( map-over-equiv-over f g i e')) ∘e
    ( equiv-ap-emb (emb-map-over-equiv-over f g i))

  htpy-eq-equiv-over :
    (e e' : equiv-over f g i) →
    ( e ＝ e') →
    ( htpy-map-over f g i
      ( map-over-equiv-over f g i e)
      ( map-over-equiv-over f g i e'))
  htpy-eq-equiv-over e e' = map-equiv (extensionality-equiv-over e e')

  eq-htpy-equiv-over :
    (e e' : equiv-over f g i) →
    htpy-map-over f g i
      ( map-over-equiv-over f g i e)
      ( map-over-equiv-over f g i e') →
    e ＝ e'
  eq-htpy-equiv-over e e' = map-inv-equiv (extensionality-equiv-over e e')
```

### Extensionality for fibered equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  extensionality-fibered-equiv :
    (e e' : fibered-equiv f g) →
    ( e ＝ e') ≃
    ( htpy-fibered-map f g
      ( fibered-map-fibered-equiv f g e)
      ( fibered-map-fibered-equiv f g e'))
  extensionality-fibered-equiv e e' =
    ( extensionality-fibered-map f g
      ( fibered-map-fibered-equiv f g e)
      ( fibered-map-fibered-equiv f g e')) ∘e
    ( equiv-ap-emb (emb-fibered-map-fibered-equiv f g))

  htpy-eq-fibered-equiv :
    (e e' : fibered-equiv f g) →
    ( e ＝ e') →
    ( htpy-fibered-map f g
      ( fibered-map-fibered-equiv f g e)
      ( fibered-map-fibered-equiv f g e'))
  htpy-eq-fibered-equiv e e' = map-equiv (extensionality-fibered-equiv e e')

  eq-htpy-fibered-equiv :
    (e e' : fibered-equiv f g) →
    htpy-fibered-map f g
      ( fibered-map-fibered-equiv f g e)
      ( fibered-map-fibered-equiv f g e') →
    e ＝ e'
  eq-htpy-fibered-equiv e e' = map-inv-equiv (extensionality-fibered-equiv e e')
```

### Fibered equivalences are pullback squares

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {Y : UU l4} (f : A → X) (g : B → Y) (ihH : fibered-map f g)
  where

  is-fibered-equiv-is-pullback :
    is-equiv (pr1 ihH) →
    is-pullback (pr1 ihH) g (cone-fibered-map f g ihH) →
    is-fibered-equiv-fibered-map f g ihH
  pr1 (is-fibered-equiv-is-pullback is-equiv-i pb) = is-equiv-i
  pr2 (is-fibered-equiv-is-pullback is-equiv-i pb) =
    is-equiv-horizontal-map-is-pullback (pr1 ihH) g
      ( cone-fibered-map f g ihH)
      ( is-equiv-i)
      ( pb)

  is-pullback-is-fibered-equiv :
    is-fibered-equiv-fibered-map f g ihH →
    is-pullback (pr1 ihH) g (cone-fibered-map f g ihH)
  is-pullback-is-fibered-equiv (is-equiv-i , is-equiv-h) =
    is-pullback-is-equiv-horizontal-maps
      (pr1 ihH) g (cone-fibered-map f g ihH) is-equiv-i is-equiv-h

  equiv-is-fibered-equiv-is-pullback :
    is-equiv (pr1 ihH) →
    is-pullback (pr1 ihH) g (cone-fibered-map f g ihH) ≃
    is-fibered-equiv-fibered-map f g ihH
  equiv-is-fibered-equiv-is-pullback is-equiv-i =
    equiv-iff-is-prop
      ( is-prop-is-pullback (pr1 ihH) g (cone-fibered-map f g ihH))
      ( is-prop-is-fibered-equiv-fibered-map f g ihH)
      ( is-fibered-equiv-is-pullback is-equiv-i)
      ( is-pullback-is-fibered-equiv)

  equiv-is-pullback-is-fibered-equiv :
    is-equiv (pr1 ihH) →
    is-fibered-equiv-fibered-map f g ihH ≃
    is-pullback (pr1 ihH) g (cone-fibered-map f g ihH)
  equiv-is-pullback-is-fibered-equiv is-equiv-i =
    inv-equiv (equiv-is-fibered-equiv-is-pullback is-equiv-i)

  fibered-equiv-is-pullback :
    is-equiv (pr1 ihH) →
    is-pullback (pr1 ihH) g (cone-fibered-map f g ihH) →
    fibered-equiv f g
  pr1 (pr1 (fibered-equiv-is-pullback is-equiv-i pb)) = pr1 ihH
  pr2 (pr1 (fibered-equiv-is-pullback is-equiv-i pb)) = is-equiv-i
  pr1 (pr1 (pr2 (fibered-equiv-is-pullback is-equiv-i pb))) = pr1 (pr2 ihH)
  pr2 (pr1 (pr2 (fibered-equiv-is-pullback is-equiv-i pb))) =
    pr2 (is-fibered-equiv-is-pullback is-equiv-i pb)
  pr2 (pr2 (fibered-equiv-is-pullback is-equiv-i pb)) = pr2 (pr2 ihH)

is-pullback-fibered-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {Y : UU l4} (f : A → X) (g : B → Y)
  (e : fibered-equiv f g) →
  is-pullback
    ( pr1 (pr1 e))
    ( g)
    ( cone-fibered-map f g (fibered-map-fibered-equiv f g e))
is-pullback-fibered-equiv f g ((i , is-equiv-i) , (h , is-equiv-h) , H) =
  is-pullback-is-fibered-equiv f g (i , h , H) (is-equiv-i , is-equiv-h)
```

## Examples

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  self-fibered-equiv : A ≃ B → fibered-equiv id id
  pr1 (self-fibered-equiv e) = e
  pr1 (pr2 (self-fibered-equiv e)) = e
  pr2 (pr2 (self-fibered-equiv e)) = refl-htpy

  id-fibered-equiv : (f : A → B) → fibered-equiv f f
  pr1 (id-fibered-equiv f) = id-equiv
  pr1 (pr2 (id-fibered-equiv f)) = id-equiv
  pr2 (pr2 (id-fibered-equiv f)) = refl-htpy

  id-fibered-equiv-htpy : (f g : A → B) → f ~ g → fibered-equiv f g
  pr1 (id-fibered-equiv-htpy f g H) = id-equiv
  pr1 (pr2 (id-fibered-equiv-htpy f g H)) = id-equiv
  pr2 (pr2 (id-fibered-equiv-htpy f g H)) = H
```

## See also

- [Equivalences of arrows](foundation.equivalences-arrows.md) for the same
  concept under a different name.
