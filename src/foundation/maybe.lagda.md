# The maybe monad

```agda
module foundation.maybe where

open import foundation-core.maybe public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equality-coproduct-types
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.surjective-maps
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation
open import foundation-core.propositions
```

</details>

## Idea

The
{{#concept "maybe monad" Disambiguation="on types" Agda=Maybe WD="option type" WDID=Q7099015}}
is an operation on types that adds one point. This is used, for example, to
define [partial functions](foundation.partial-functions.md), where a partial
function `f : X ⇀ Y` is a map `f : X → Maybe Y`.

The maybe monad is an example of a monad that is not a
[modality](orthogonal-factorization-systems.higher-modalities.md), since it is
not [idempotent](foundation.idempotent-maps.md).

## Properties

### The unit of `Maybe` is an embedding

```agda
abstract
  is-emb-unit-Maybe : {l : Level} {X : UU l} → is-emb (unit-Maybe {X = X})
  is-emb-unit-Maybe = is-emb-inl

emb-unit-Maybe : {l : Level} (X : UU l) → X ↪ Maybe X
pr1 (emb-unit-Maybe X) = unit-Maybe
pr2 (emb-unit-Maybe X) = is-emb-unit-Maybe

abstract
  is-injective-unit-Maybe :
    {l : Level} {X : UU l} → is-injective (unit-Maybe {X = X})
  is-injective-unit-Maybe = is-injective-inl
```

### Being an exception is a decidable proposition

```agda
module _
  {l : Level} {X : UU l}
  where

  is-decidable-is-exception-Maybe :
    (x : Maybe X) → is-decidable (is-exception-Maybe x)
  is-decidable-is-exception-Maybe (inl x) =
    inr (λ p → ex-falso (is-empty-eq-coproduct-inl-inr x star p))
  is-decidable-is-exception-Maybe (inr star) = inl refl

  is-decidable-is-not-exception-Maybe :
    (x : Maybe X) → is-decidable (is-not-exception-Maybe x)
  is-decidable-is-not-exception-Maybe x =
    is-decidable-neg (is-decidable-is-exception-Maybe x)
```

### If a point is not an exception, then it is a value

```agda
is-value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) →
  is-not-exception-Maybe x → is-value-Maybe x
is-value-is-not-exception-Maybe x H =
  map-right-unit-law-coproduct-is-empty
    ( is-value-Maybe x)
    ( is-exception-Maybe x)
    ( H)
    ( decide-Maybe x)

value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) → is-not-exception-Maybe x → X
value-is-not-exception-Maybe x H =
  value-is-value-Maybe x (is-value-is-not-exception-Maybe x H)

eq-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) (H : is-not-exception-Maybe x) →
  inl (value-is-not-exception-Maybe x H) ＝ x
eq-is-not-exception-Maybe x H =
  eq-is-value-Maybe x (is-value-is-not-exception-Maybe x H)
```

### The unit of `Maybe` is not surjective

```agda
abstract
  is-not-surjective-unit-Maybe :
    {l : Level} {X : UU l} → ¬ (is-surjective (unit-Maybe {X = X}))
  is-not-surjective-unit-Maybe H =
    rec-trunc-Prop empty-Prop
      ( λ p → is-not-exception-unit-Maybe (pr1 p) (pr2 p))
      ( H exception-Maybe)
```

### The extension of surjective maps is surjective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-surjective-extend-is-surjective-Maybe :
    {f : A → Maybe B} → is-surjective f → is-surjective (extend-Maybe f)
  is-surjective-extend-is-surjective-Maybe {f} F y =
    elim-exists
      ( exists-structure-Prop (Maybe A) (λ z → extend-Maybe f z ＝ y))
      ( λ x p → intro-exists (inl x) p)
      ( F y)
```

### The functorial action of `Maybe` preserves surjective maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-surjective-map-is-surjective-Maybe :
    {f : A → B} → is-surjective f → is-surjective (map-Maybe f)
  is-surjective-map-is-surjective-Maybe {f} F (inl y) =
    elim-exists
      ( exists-structure-Prop (Maybe A) (λ z → map-Maybe f z ＝ inl y))
      ( λ x p → intro-exists (inl x) (ap inl p))
      ( F y)
  is-surjective-map-is-surjective-Maybe F (inr *) = intro-exists (inr *) refl
```

### There is a surjection from `Maybe A + Maybe B` to `Maybe (A + B)`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-surjective-map-maybe-coproduct :
    is-surjective (map-maybe-coproduct {A = A} {B})
  is-surjective-map-maybe-coproduct (inl (inl x)) =
    unit-trunc-Prop ((inl (inl x)) , refl)
  is-surjective-map-maybe-coproduct (inl (inr x)) =
    unit-trunc-Prop ((inr (inl x)) , refl)
  is-surjective-map-maybe-coproduct (inr star) =
    unit-trunc-Prop ((inl (inr star)) , refl)
```

### There is a surjection from `Maybe A × Maybe B` to `Maybe (A × B)`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-surjective-map-maybe-product :
    is-surjective (map-maybe-product {A = A} {B})
  is-surjective-map-maybe-product (inl (a , b)) =
    unit-trunc-Prop ((inl a , inl b) , refl)
  is-surjective-map-maybe-product (inr star) =
    unit-trunc-Prop ((inr star , inr star) , refl)
```

## External links

- [maybe monad](https://ncatlab.org/nlab/show/maybe+monad) at $n$Lab
- [Monad (category theory)#The maybe monad](<https://en.wikipedia.org/wiki/Monad_(category_theory)#The_maybe_monad>)
  at Wikipedia
- [Option type](https://en.wikipedia.org/wiki/Option_type) at Wikipedia
