# Pointed maps

```agda
module structured-types.pointed-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import structured-types.pointed-dependent-functions
open import structured-types.pointed-families-of-types
open import structured-types.pointed-types
```

</details>

## Idea

A {{#concept "pointed map" Agda=pointed-map}} from a
[pointed type](structured-types.pointed-types.md) `A` to a pointed type `B` is a
base point preserving function from `A` to `B`.

The type `A →∗ B` of pointed maps from `A` to `B` is itself pointed by the
[constant pointed map](structured-types.constant-pointed-maps.md).

## Definitions

### Pointed maps

```agda
module _
  {l1 l2 : Level}
  where

  pointed-map : Pointed-Type l1 → Pointed-Type l2 → UU (l1 ⊔ l2)
  pointed-map A B = pointed-Π A (constant-Pointed-Fam A B)

  infixr 5 _→∗_
  _→∗_ = pointed-map
```

**Note**: the subscript asterisk symbol used for the pointed map type `_→∗_`,
and pointed type constructions in general, is the
[asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input: `\ast`), not
the [asterisk](https://codepoints.net/U+002A) `*`.

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  map-pointed-map : A →∗ B → type-Pointed-Type A → type-Pointed-Type B
  map-pointed-map = pr1

  preserves-point-pointed-map :
    (f : A →∗ B) →
    map-pointed-map f (point-Pointed-Type A) ＝ point-Pointed-Type B
  preserves-point-pointed-map = pr2
```

### Precomposing pointed maps

```agda
module _
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (C : Pointed-Fam l3 B) (f : A →∗ B)
  where

  precomp-Pointed-Fam : Pointed-Fam l3 A
  pr1 precomp-Pointed-Fam = fam-Pointed-Fam B C ∘ map-pointed-map f
  pr2 precomp-Pointed-Fam =
    tr
      ( fam-Pointed-Fam B C)
      ( inv (preserves-point-pointed-map f))
      ( point-Pointed-Fam B C)

  precomp-pointed-Π : pointed-Π B C → pointed-Π A precomp-Pointed-Fam
  pr1 (precomp-pointed-Π g) x =
    function-pointed-Π g (map-pointed-map f x)
  pr2 (precomp-pointed-Π g) =
    ( inv
      ( apd
        ( function-pointed-Π g)
        ( inv (preserves-point-pointed-map f)))) ∙
    ( ap
      ( tr
        ( fam-Pointed-Fam B C)
        ( inv (preserves-point-pointed-map f)))
      ( preserves-point-function-pointed-Π g))
```

### Composing pointed maps

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  where

  map-comp-pointed-map :
    B →∗ C → A →∗ B → type-Pointed-Type A → type-Pointed-Type C
  map-comp-pointed-map g f =
    map-pointed-map g ∘ map-pointed-map f

  preserves-point-comp-pointed-map :
    (g : B →∗ C) (f : A →∗ B) →
    (map-comp-pointed-map g f (point-Pointed-Type A)) ＝ point-Pointed-Type C
  preserves-point-comp-pointed-map g f =
    ( ap (map-pointed-map g) (preserves-point-pointed-map f)) ∙
    ( preserves-point-pointed-map g)

  comp-pointed-map : B →∗ C → A →∗ B → A →∗ C
  pr1 (comp-pointed-map g f) = map-comp-pointed-map g f
  pr2 (comp-pointed-map g f) = preserves-point-comp-pointed-map g f

  infixr 15 _∘∗_

  _∘∗_ : B →∗ C → A →∗ B → A →∗ C
  _∘∗_ = comp-pointed-map
```

### The identity pointed map

```agda
module _
  {l1 : Level} {A : Pointed-Type l1}
  where

  id-pointed-map : A →∗ A
  pr1 id-pointed-map = id
  pr2 id-pointed-map = refl
```

### Truncatedness of the type of pointed maps

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where abstract

  is-trunc-pointed-function-type :
    (k : 𝕋) → is-trunc k (type-Pointed-Type B) → is-trunc k (pointed-map A B)
  is-trunc-pointed-function-type k H =
    is-trunc-Σ
      ( is-trunc-function-type k H)
      ( λ f → is-trunc-Id H (f (point-Pointed-Type A)) (point-Pointed-Type B))
```

## See also

- [Constant pointed maps](structured-types.constant-pointed-maps.md)
- [Precomposition of pointed maps](structured-types.precomposition-pointed-maps.md)
