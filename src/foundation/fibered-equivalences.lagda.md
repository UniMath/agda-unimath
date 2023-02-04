---
title: Fibered equivalences
---

```agda
module foundation.fibered-equivalences where

open import foundation-core.cartesian-product-types
open import foundation-core.cones-pullbacks
open import foundation-core.dependent-pair-types
open import foundation-core.fibers-of-maps
open import foundation-core.functions
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.slice
open import foundation-core.subtypes
open import foundation-core.type-arithmetic-dependent-pair-types
open import foundation-core.type-arithmetic-cartesian-product-types
open import foundation-core.universe-levels

open import foundation.embeddings
open import foundation.equational-reasoning
open import foundation.equivalences
open import foundation.fibered-maps
open import foundation.functoriality-cartesian-product-types
open import foundation.pullbacks
```

## Idea

A fibered equivalence is a fibered map

```md
       h
  A -------> B
  |          |
 f|          |g
  |          |
  V          V
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
    Σ (fiberwise-map-over f g i) (is-fiberwise-equiv)

  fam-equiv-over : (X → Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fam-equiv-over i = (x : X) → (fib f x) ≃ (fib g (i x))
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
    fiberwise-equiv (fib (i ∘ f)) (fib g) ≃ equiv-over f g i
  equiv-equiv-over-fiberwise-equiv =
    equiv-equiv-slice-fiberwise-equiv (i ∘ f) g
```

### Fibered equivalences embed into the type of fibered maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (i : X → Y)
  where

  equiv-Σ-is-equiv-equiv-over :
    (equiv-over f g i) ≃ Σ (map-over f g i) (is-equiv ∘ pr1)
  equiv-Σ-is-equiv-equiv-over = equivalence-reasoning
    Σ (A ≃ B) (is-map-over f g i ∘ pr1)
      ≃ Σ (A → B) (λ h → is-equiv h × is-map-over f g i h)
        by assoc-Σ (A → B) is-equiv (is-map-over f g i ∘ pr1)
      ≃ Σ (A → B) (λ h → is-map-over f g i h × is-equiv h)
        by equiv-tot (λ _ → commutative-prod)
      ≃ Σ (Σ (A → B) (is-map-over f g i)) (is-equiv ∘ pr1)
        by inv-assoc-Σ (A → B) (is-map-over f g i) (is-equiv ∘ pr1)
  
  emb-map-over-equiv-over : equiv-over f g i ↪ map-over f g i
  emb-map-over-equiv-over =
    comp-emb
      ( emb-subtype (is-equiv-Prop ∘ pr1))
      ( emb-equiv equiv-Σ-is-equiv-equiv-over)

  map-emb-map-over-equiv-over : equiv-over f g i → map-over f g i
  map-emb-map-over-equiv-over = map-emb emb-map-over-equiv-over

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  is-fibered-equiv-fibered-map : fibered-map f g → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-fibered-equiv-fibered-map (i , h , H) = is-equiv i × is-equiv h

  is-prop-is-fibered-equiv-fibered-map :
    (ihH : fibered-map f g) → is-prop (is-fibered-equiv-fibered-map ihH)
  is-prop-is-fibered-equiv-fibered-map (i , h , H) =
    is-prop-prod (is-property-is-equiv i) (is-property-is-equiv h)

  is-fibered-equiv-fibered-map-Prop :
    fibered-map f g → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-fibered-equiv-fibered-map-Prop ihH =
    pair
      ( is-fibered-equiv-fibered-map ihH)
      ( is-prop-is-fibered-equiv-fibered-map ihH)

  equiv-Σ-is-fibered-equiv-fibered-map-fibered-equiv :
    (fibered-equiv f g) ≃ Σ (fibered-map f g) (is-fibered-equiv-fibered-map)
  equiv-Σ-is-fibered-equiv-fibered-map-fibered-equiv = equivalence-reasoning
    Σ (X ≃ Y) (λ (i , _) → Σ (A ≃ B) (λ (h , _) → is-map-over f g i h))
      ≃ Σ (X ≃ Y) (λ (i , _) → Σ (map-over f g i) (λ (h , _) → is-equiv h))
        by equiv-tot (λ (i , _) → equiv-Σ-is-equiv-equiv-over f g i)
      ≃ Σ (Σ (X ≃ Y) (λ (i , _) → map-over f g i)) (λ (_ , h , H) → is-equiv h)
        by inv-assoc-Σ (X ≃ Y) (λ (i , _) → map-over f g i) (λ (_ , h , H) → is-equiv h)
      ≃ Σ (Σ (X → Y) (λ i → is-equiv i × map-over f g i)) (λ (i , _ , h , H) → is-equiv h)
        by equiv-Σ-equiv-base _ (assoc-Σ (X → Y) is-equiv (λ (i , _) → map-over f g i))
      ≃ Σ (Σ (X → Y) (λ i → map-over f g i × is-equiv i)) (λ (i , (h , H) , _) → is-equiv h)
        by equiv-Σ-equiv-base _ (equiv-tot (λ _ → commutative-prod))
      ≃ Σ (Σ ( Σ (X → Y) (map-over f g)) (λ (i , _) → is-equiv i)) (λ ((i , h , H) , _) → is-equiv h)
        by equiv-Σ-equiv-base _ (inv-assoc-Σ (X → Y) (map-over f g) (λ (i , _) → is-equiv i))
      ≃ Σ (Σ (X → Y) (map-over f g)) (λ (i , h , H) → is-equiv i × is-equiv h)
        by assoc-Σ (Σ (X → Y) (map-over f g)) (λ (i , h , H) → is-equiv i) (λ ((i , h , H) , _) → is-equiv h)

  emb-fibered-map-fibered-equiv : fibered-equiv f g ↪ fibered-map f g
  emb-fibered-map-fibered-equiv =
    comp-emb
      ( emb-subtype is-fibered-equiv-fibered-map-Prop)
      ( emb-equiv equiv-Σ-is-fibered-equiv-fibered-map-fibered-equiv)
  
  map-emb-fibered-map-fibered-equiv : fibered-equiv f g → fibered-map f g
  map-emb-fibered-map-fibered-equiv = map-emb emb-fibered-map-fibered-equiv
```

## Examples

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  fibered-equiv-self : A ≃ B → fibered-equiv id id
  fibered-equiv-self e = e , e , refl-htpy

  fibered-equiv-id : (f : A → B) → fibered-equiv f f
  fibered-equiv-id f = id-equiv , id-equiv , refl-htpy

  fibered-equiv-id-htpy : (f g : A → B) → f ~ g → fibered-equiv f g
  fibered-equiv-id-htpy f g H = id-equiv , id-equiv , H
```

### Fibered equivalences are pullback squares

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {Y : UU l4} (f : A → X) (g : B → Y) ((i , h , H) : fibered-map f g)
  where
  
  is-fibered-equiv-is-pullback :
    is-equiv i →
    is-pullback i g (cone-fibered-map f g (i , h , H)) →
    is-fibered-equiv-fibered-map f g (i , h , H)
  is-fibered-equiv-is-pullback is-equiv-i pb =
    is-equiv-i , is-equiv-is-pullback' i g (cone-fibered-map f g (i , h , H)) is-equiv-i pb

  is-pullback-is-fibered-equiv :
    is-fibered-equiv-fibered-map f g (i , h , H) →
    is-pullback i g (cone-fibered-map f g (i , h , H))
  is-pullback-is-fibered-equiv (is-equiv-i , is-equiv-h) =
    is-pullback-is-equiv' i g (cone-fibered-map f g (i , h , H)) is-equiv-i is-equiv-h

  equiv-is-fibered-equiv-is-pullback :
    is-equiv i →
    is-pullback i g (cone-fibered-map f g (i , h , H)) ≃
    is-fibered-equiv-fibered-map f g (i , h , H)
  equiv-is-fibered-equiv-is-pullback is-equiv-i =
    equiv-prop
      ( is-property-is-pullback i g (cone-fibered-map f g (i , h , H)))
      ( is-prop-is-fibered-equiv-fibered-map f g (i , h , H))
      ( is-fibered-equiv-is-pullback is-equiv-i)
      ( is-pullback-is-fibered-equiv)

  equiv-is-pullback-is-fibered-equiv :
    is-equiv i →
    is-fibered-equiv-fibered-map f g (i , h , H) ≃
    is-pullback i g (cone-fibered-map f g (i , h , H))
  equiv-is-pullback-is-fibered-equiv is-equiv-i =
    inv-equiv (equiv-is-fibered-equiv-is-pullback is-equiv-i)

  fibered-equiv-is-pullback : 
    is-equiv i → 
    is-pullback i g (cone-fibered-map f g (i , h , H)) →
    fibered-equiv f g
  fibered-equiv-is-pullback is-equiv-i pb =
    (i , is-equiv-i) , (h , pr2 (is-fibered-equiv-is-pullback is-equiv-i pb)) , H
is-pullback-fibered-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {Y : UU l4} (f : A → X) (g : B → Y)
  (((i , _) , (h , _) , H) : fibered-equiv f g) →
  is-pullback i g (cone-fibered-map f g (i , h , H))
is-pullback-fibered-equiv f g ((i , is-equiv-i) , (h , is-equiv-h) , H) =
  is-pullback-is-fibered-equiv f g (i , h , H) (is-equiv-i , is-equiv-h)
```
