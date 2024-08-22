# `0`-Connected types

```agda
module foundation.0-connected-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.fiber-inclusions
open import foundation.functoriality-set-truncation
open import foundation.images
open import foundation.inhabited-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.set-truncations
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universal-property-contractible-types
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.propositions
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A type is said to be {{#concept "0-connected" Agda=is-0-connected}} if its type
of connected components, i.e., its
[set truncation](foundation.set-truncations.md), is
[contractible](foundation-core.contractible-types.md). Sometimes we simply say
that a type is connected instead of saying that it is 0-connected.

## Definitions

### The predicate of being a `0`-connected type

```agda
module _
  {l : Level} (A : UU l)
  where

  is-0-connected-Prop : Prop l
  is-0-connected-Prop = is-contr-Prop (type-trunc-Set A)

  is-0-connected : UU l
  is-0-connected = type-Prop is-0-connected-Prop

  is-prop-is-0-connected : is-prop is-0-connected
  is-prop-is-0-connected = is-prop-type-Prop is-0-connected-Prop
```

### The dependent universal property of pointed `0`-connected types

The
{{#concept "dependent universal property of `0`-connected types" Agda=dependent-universal-property-0-connected-type}}
asserts that for any element `a` in a type `A` and any
[subtype](foundation.subtypes.md) `P` of `A`, the evaluation map

```text
  ((x : A) → P x) → P a
```

is an equivalence. In other words, a type `A` with a given element `a` is
`0`-connected precisely when any subtype contains all elements if and only if it
contains the given element `a`.

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  ev-point-subtype :
    {l2 : Level} (P : subtype l2 A) →
    ((x : A) → is-in-subtype P x) → is-in-subtype P a
  ev-point-subtype P f = f a

  dependent-universal-property-0-connected-type : UUω
  dependent-universal-property-0-connected-type =
    {l : Level} (P : subtype l A) → is-equiv (ev-point-subtype P)
```

### The universal property of `0`-connected types

The
{{#concept "universal property of `0`-connected types" Agda=universal-property-0-connected-type}}
asserts that maps from a type `A` equipped with a given element `a : A` into a
[set](foundation-core.sets.md) `S` are uniquely determined by an element of `S`.

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  universal-property-0-connected-type : UUω
  universal-property-0-connected-type =
    {l : Level} (S : Set l) → is-equiv (ev-point' a {type-Set S})
```

## Properties

### `0`-connected types are inhabited

```agda
abstract
  is-inhabited-is-0-connected :
    {l : Level} {A : UU l} → is-0-connected A → is-inhabited A
  is-inhabited-is-0-connected {l} {A} C =
    apply-universal-property-trunc-Set'
      ( center C)
      ( set-Prop (trunc-Prop A))
      ( unit-trunc-Prop)
```

### Any two elements in a `0`-connected type are merely equal

```agda
abstract
  mere-eq-is-0-connected :
    {l : Level} {A : UU l} → is-0-connected A → (x y : A) → mere-eq x y
  mere-eq-is-0-connected {A = A} H x y =
    apply-effectiveness-unit-trunc-Set (eq-is-contr H)
```

### A pointed type in which every element is merely equal to the base point is `0`-connected

```agda
abstract
  is-0-connected-mere-eq :
    {l : Level} {A : UU l} (a : A) →
    ((x : A) → mere-eq a x) → is-0-connected A
  pr1 (is-0-connected-mere-eq {l} {A} a e) =
    unit-trunc-Set a
  pr2 (is-0-connected-mere-eq {l} {A} a e) =
    apply-dependent-universal-property-trunc-Set'
      ( λ x → set-Prop (Id-Prop (trunc-Set A) (unit-trunc-Set a) x))
      ( λ x → apply-effectiveness-unit-trunc-Set' (e x))
```

### An inhabited type in which any two elements are merely equal is `0`-connected

```agda
abstract
  is-0-connected-mere-eq-is-inhabited :
    {l : Level} {A : UU l} →
    is-inhabited A → ((x y : A) → mere-eq x y) → is-0-connected A
  is-0-connected-mere-eq-is-inhabited H K =
    apply-universal-property-trunc-Prop H
      ( is-0-connected-Prop _)
      ( λ a → is-0-connected-mere-eq a (K a))
```

### The point inclusion of a given element of a type is surjective if and only if the type is `0`-connected

```agda
abstract
  is-0-connected-is-surjective-point :
    {l1 : Level} {A : UU l1} (a : A) →
    is-surjective (point a) → is-0-connected A
  is-0-connected-is-surjective-point a H =
    is-0-connected-mere-eq a
      ( λ x →
        apply-universal-property-trunc-Prop
          ( H x)
          ( mere-eq-Prop a x)
          ( λ u → unit-trunc-Prop (pr2 u)))

abstract
  is-surjective-point-is-0-connected :
    {l1 : Level} {A : UU l1} (a : A) →
    is-0-connected A → is-surjective (point a)
  is-surjective-point-is-0-connected a H x =
    apply-universal-property-trunc-Prop
      ( mere-eq-is-0-connected H a x)
      ( trunc-Prop (fiber (point a) x))
      ( λ where refl → unit-trunc-Prop (star , refl))
```

### A pointed connected type `A` is `k + 1`-truncated if and only if the base point inclusion is `k`-truncated

```agda
abstract
  is-trunc-map-ev-point-is-connected :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (a : A) →
    is-0-connected A → is-trunc (succ-𝕋 k) B →
    is-trunc-map k (ev-point' a {B})
  is-trunc-map-ev-point-is-connected k {A} {B} a H K =
    is-trunc-map-comp k
      ( ev-point' star {B})
      ( precomp (point a) B)
      ( is-trunc-map-is-equiv k
        ( universal-property-contr-is-contr star is-contr-unit B))
      ( is-trunc-map-precomp-Π-is-surjective k
        ( is-surjective-point-is-0-connected a H)
        ( λ _ → (B , K)))
```

### The dependent universal property of `0`-connected types

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  abstract
    is-0-connected-dependent-universal-property-0-connected-type :
      dependent-universal-property-0-connected-type a →
      is-0-connected A
    is-0-connected-dependent-universal-property-0-connected-type H =
      is-0-connected-mere-eq a
        ( map-inv-is-equiv (H (mere-eq-Prop a)) (refl-mere-eq a))

  abstract
    dependent-universal-property-0-connected-type-is-0-connected :
      is-0-connected A → dependent-universal-property-0-connected-type a
    dependent-universal-property-0-connected-type-is-0-connected H P =
      is-equiv-comp _ _
        ( dependent-universal-property-surjection-is-surjective
          ( point a)
          ( is-surjective-point-is-0-connected a H)
          ( P))
        ( universal-property-unit (type-Prop (P a)))

  equiv-dependent-universal-property-0-connected-type :
    is-0-connected A →
    ( {l : Level} (P : subtype l A) →
      ((x : A) → is-in-subtype P x) ≃ is-in-subtype P a)
  equiv-dependent-universal-property-0-connected-type H P =
    ( equiv-universal-property-unit (type-Prop (P a))) ∘e
    ( equiv-dependent-universal-property-surjection-is-surjective
      ( point a)
      ( is-surjective-point-is-0-connected a H)
      ( P))

  abstract
    apply-dependent-universal-property-0-connected-type :
      {l2 : Level} → is-0-connected A → (P : subtype l2 A) →
      is-in-subtype P a → (x : A) → is-in-subtype P x
    apply-dependent-universal-property-0-connected-type H P =
      map-inv-equiv (equiv-dependent-universal-property-0-connected-type H P)
```

### A pointed type is connected if and only if the fiber inclusion is surjective for any type family over it

```agda
abstract
  is-surjective-fiber-inclusion :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-0-connected A → (a : A) → is-surjective (fiber-inclusion B a)
  is-surjective-fiber-inclusion {B = B} C a (x , b) =
    apply-universal-property-trunc-Prop
      ( mere-eq-is-0-connected C a x)
      ( trunc-Prop (fiber (fiber-inclusion B a) (x , b)))
      ( λ where refl → unit-trunc-Prop (b , refl))

abstract
  mere-eq-is-surjective-fiber-inclusion :
    {l1 : Level} {A : UU l1} (a : A) →
    ({l : Level} (B : A → UU l) → is-surjective (fiber-inclusion B a)) →
    (x : A) → mere-eq a x
  mere-eq-is-surjective-fiber-inclusion a H x =
    apply-universal-property-trunc-Prop
      ( H (λ x → unit) (x , star))
      ( mere-eq-Prop a x)
      ( λ u → unit-trunc-Prop (ap pr1 (pr2 u)))

abstract
  is-0-connected-is-surjective-fiber-inclusion :
    {l1 : Level} {A : UU l1} (a : A) →
    ({l : Level} (B : A → UU l) → is-surjective (fiber-inclusion B a)) →
    is-0-connected A
  is-0-connected-is-surjective-fiber-inclusion a H =
    is-0-connected-mere-eq a (mere-eq-is-surjective-fiber-inclusion a H)
```

### `0`-connected types are closed under equivalences

```agda
abstract
  is-0-connected-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    (A ≃ B) → is-0-connected B → is-0-connected A
  is-0-connected-equiv e = is-contr-equiv _ (equiv-trunc-Set e)

abstract
  is-0-connected-equiv' :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    (A ≃ B) → is-0-connected A → is-0-connected B
  is-0-connected-equiv' e = is-0-connected-equiv (inv-equiv e)
```

### `0`-connected types are closed under cartesian products

```agda
module _
  {l1 l2 : Level} (X : UU l1) (Y : UU l2)
  (p1 : is-0-connected X) (p2 : is-0-connected Y)
  where

  is-0-connected-product : is-0-connected (X × Y)
  is-0-connected-product =
    is-contr-equiv
      ( type-trunc-Set X × type-trunc-Set Y)
      ( equiv-distributive-trunc-product-Set X Y)
      ( is-contr-product p1 p2)
```

### The unit type is `0`-connected

```agda
abstract
  is-0-connected-unit : is-0-connected unit
  is-0-connected-unit =
    is-contr-equiv' unit equiv-unit-trunc-unit-Set is-contr-unit
```

### A contractible type is `0`-connected

```agda
abstract
  is-0-connected-is-contr :
    {l : Level} (X : UU l) →
    is-contr X → is-0-connected X
  is-0-connected-is-contr X p =
    is-contr-equiv X
      ( inv-equiv (equiv-unit-trunc-Set (X , is-set-is-contr p)))
      ( p)
```

### The image of a function with a `0`-connected domain is `0`-connected

```agda
abstract
  is-0-connected-im-is-0-connected-domain :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-0-connected A → is-0-connected (im f)
  is-0-connected-im-is-0-connected-domain {A = A} {B} f C =
    apply-universal-property-trunc-Prop
      ( is-inhabited-is-0-connected C)
      ( is-contr-Prop _)
      ( λ a →
        is-contr-equiv'
          ( im (map-trunc-Set f))
          ( equiv-trunc-im-Set f)
          ( is-contr-im
            ( trunc-Set B)
            ( unit-trunc-Set a)
            ( apply-dependent-universal-property-trunc-Set'
              ( λ x →
                set-Prop
                  ( Id-Prop
                    ( trunc-Set B)
                    ( map-trunc-Set f x)
                    ( map-trunc-Set f (unit-trunc-Set a))))
              ( λ a' →
                apply-universal-property-trunc-Prop
                  ( mere-eq-is-0-connected C a' a)
                  ( Id-Prop
                    ( trunc-Set B)
                    ( map-trunc-Set f (unit-trunc-Set a'))
                    ( map-trunc-Set f (unit-trunc-Set a)))
                  ( λ where refl → refl)))))

abstract
  is-0-connected-im-point' :
    {l1 : Level} {A : UU l1} (f : unit → A) → is-0-connected (im f)
  is-0-connected-im-point' f =
    is-0-connected-im-is-0-connected-domain f is-0-connected-unit
```
