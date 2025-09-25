# The maybe monad

```agda
module foundation.maybe where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equality-coproduct-types
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
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

## Definitions

### The maybe monad

```agda
Maybe : {l : Level} → UU l → UU l
Maybe X = X + unit

unit-Maybe : {l : Level} {X : UU l} → X → Maybe X
unit-Maybe = inl

exception-Maybe : {l : Level} {X : UU l} → Maybe X
exception-Maybe = inr star

extend-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Maybe Y) → Maybe X → Maybe Y
extend-Maybe f (inl x) = f x
extend-Maybe f (inr *) = inr *

map-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Y) → Maybe X → Maybe Y
map-Maybe f (inl x) = inl (f x)
map-Maybe f (inr *) = inr *
```

### The inductive definition of the maybe monad

```agda
data Maybe' {l : Level} (X : UU l) : UU l where
  unit-Maybe' : X → Maybe' X
  exception-Maybe' : Maybe' X

{-# BUILTIN MAYBE Maybe' #-}
```

### The predicate of being an exception

```agda
is-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-exception-Maybe {l} {X} x = (x ＝ exception-Maybe)

is-not-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-not-exception-Maybe x = ¬ (is-exception-Maybe x)

is-prop-is-exception-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-prop (is-exception-Maybe x)
is-prop-is-exception-Maybe (inl x) ()
is-prop-is-exception-Maybe (inr x) =
  is-prop-equiv (compute-eq-coproduct-inr-inr x star) (is-set-unit x star)
```

### The predicate of being a value

```agda
is-value-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-value-Maybe {l} {X} x = Σ X (λ y → inl y ＝ x)

value-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-value-Maybe x → X
value-is-value-Maybe x = pr1

eq-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) (H : is-value-Maybe x) →
  inl (value-is-value-Maybe x H) ＝ x
eq-is-value-Maybe x H = pr2 H
```

### Maybe structure on a type

```agda
maybe-structure : {l1 : Level} (X : UU l1) → UU (lsuc l1)
maybe-structure {l1} X = Σ (UU l1) (λ Y → Maybe Y ≃ X)
```

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

### The values of the unit of the `Maybe` monad are not exceptions

```agda
abstract
  is-not-exception-unit-Maybe :
    {l : Level} {X : UU l} (x : X) → is-not-exception-Maybe (unit-Maybe x)
  is-not-exception-unit-Maybe x ()
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

### For any element of type `Maybe X` we can decide whether it is a value or an exception

```agda
decide-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-value-Maybe x + is-exception-Maybe x
decide-Maybe (inl x) = inl (x , refl)
decide-Maybe (inr star) = inr refl
```

### Values are not exceptions

```agda
abstract
  is-not-exception-is-value-Maybe :
    {l1 : Level} {X : UU l1} (x : Maybe X) →
    is-value-Maybe x → is-not-exception-Maybe x
  is-not-exception-is-value-Maybe {l1} {X} .(inl x) (x , refl) =
    is-not-exception-unit-Maybe x
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

### The two definitions of `Maybe` are equivalent

```agda
module _
  {l1 l2 : Level} {X : UU l1}
  where

  map-Maybe-Maybe' : Maybe X → Maybe' X
  map-Maybe-Maybe' (inl x) = unit-Maybe' x
  map-Maybe-Maybe' (inr _) = exception-Maybe'

  map-inv-Maybe-Maybe' : Maybe' X → Maybe X
  map-inv-Maybe-Maybe' (unit-Maybe' x) = inl x
  map-inv-Maybe-Maybe' exception-Maybe' = inr star

  is-section-map-inv-Maybe-Maybe' :
    is-section map-Maybe-Maybe' map-inv-Maybe-Maybe'
  is-section-map-inv-Maybe-Maybe' (unit-Maybe' x) = refl
  is-section-map-inv-Maybe-Maybe' exception-Maybe' = refl

  is-retraction-map-inv-Maybe-Maybe' :
    is-retraction map-Maybe-Maybe' map-inv-Maybe-Maybe'
  is-retraction-map-inv-Maybe-Maybe' (inl x) = refl
  is-retraction-map-inv-Maybe-Maybe' (inr x) = refl

  is-equiv-map-Maybe-Maybe' : is-equiv map-Maybe-Maybe'
  is-equiv-map-Maybe-Maybe' =
    is-equiv-is-invertible
      ( map-inv-Maybe-Maybe')
      ( is-section-map-inv-Maybe-Maybe')
      ( is-retraction-map-inv-Maybe-Maybe')

  equiv-Maybe-Maybe' : Maybe X ≃ Maybe' X
  equiv-Maybe-Maybe' = (map-Maybe-Maybe' , is-equiv-map-Maybe-Maybe')
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

  surjection-map-surjection-Maybe : (f : A ↠ B) → Maybe A ↠ Maybe B
  surjection-map-surjection-Maybe (f , is-surjective-f) =
    ( map-Maybe f , is-surjective-map-is-surjective-Maybe is-surjective-f)
```

### There is a surjection from `Maybe A + Maybe B` to `Maybe (A + B)`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-maybe-coproduct : Maybe A + Maybe B → Maybe (A + B)
  map-maybe-coproduct (inl (inl x)) = inl (inl x)
  map-maybe-coproduct (inl (inr star)) = inr star
  map-maybe-coproduct (inr (inl x)) = inl (inr x)
  map-maybe-coproduct (inr (inr star)) = inr star

  is-surjective-map-maybe-coproduct : is-surjective map-maybe-coproduct
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

  map-maybe-product : Maybe A × Maybe B → Maybe (A × B)
  map-maybe-product (inl a , inl b) = inl (a , b)
  map-maybe-product (inl a , inr star) = inr star
  map-maybe-product (inr star , inl b) = inr star
  map-maybe-product (inr star , inr star) = inr star

  is-surjective-map-maybe-product : is-surjective map-maybe-product
  is-surjective-map-maybe-product (inl (a , b)) =
    unit-trunc-Prop ((inl a , inl b) , refl)
  is-surjective-map-maybe-product (inr star) =
    unit-trunc-Prop ((inr star , inr star) , refl)
```

### If `X` is a set, `Maybe X` is a set

```agda
maybe-Set : {l : Level} (X : Set l) → Set l
maybe-Set X = coproduct-Set X unit-Set
```

## External links

- [maybe monad](https://ncatlab.org/nlab/show/maybe+monad) at $n$Lab
- [Monad (category theory)#The maybe monad](<https://en.wikipedia.org/wiki/Monad_(category_theory)#The_maybe_monad>)
  at Wikipedia
- [Option type](https://en.wikipedia.org/wiki/Option_type) at Wikipedia
