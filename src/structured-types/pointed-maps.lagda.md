# Pointed maps

```agda
module structured-types.pointed-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-dependent-functions
open import structured-types.pointed-families-of-types
open import structured-types.pointed-types
```

</details>

## Idea

A pointed map from a pointed type `A` to a pointed type `B` is a base point
preserving function from `A` to `B`.

## Definitions

### Pointed maps

```agda
module _
  {l1 l2 : Level}
  where

  pointed-map : Pointed-Type l1 → Pointed-Type l2 → UU (l1 ⊔ l2)
  pointed-map A B = pointed-Π A (constant-Pointed-Fam A B)

  _→∗_ = pointed-map
```

**Note**: the subscript asterisk symbol used for the pointed map type `_→∗_`,
and pointed type constructions in general, is the
[asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input: `\ast`), not
the [asterisk](https://codepoints.net/U+002A) `*`.

```agda
  constant-pointed-map : (A : Pointed-Type l1) (B : Pointed-Type l2) → A →∗ B
  pr1 (constant-pointed-map A B) =
    const (type-Pointed-Type A) (type-Pointed-Type B) (point-Pointed-Type B)
  pr2 (constant-pointed-map A B) = refl

  pointed-map-Pointed-Type :
    Pointed-Type l1 → Pointed-Type l2 → Pointed-Type (l1 ⊔ l2)
  pr1 (pointed-map-Pointed-Type A B) = pointed-map A B
  pr2 (pointed-map-Pointed-Type A B) = constant-pointed-map A B

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
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
  {l1 l2 l3 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  (C : Pointed-Fam l3 B) (f : A →∗ B)
  where

  precomp-Pointed-Fam : Pointed-Fam l3 A
  pr1 precomp-Pointed-Fam = fam-Pointed-Fam B C ∘ map-pointed-map A B f
  pr2 precomp-Pointed-Fam =
    tr
      ( fam-Pointed-Fam B C)
      ( inv (preserves-point-pointed-map A B f))
      ( point-Pointed-Fam B C)

  precomp-pointed-Π : pointed-Π B C → pointed-Π A precomp-Pointed-Fam
  pr1 (precomp-pointed-Π g) x =
    function-pointed-Π B C g (map-pointed-map A B f x)
  pr2 (precomp-pointed-Π g) =
    ( inv
      ( apd
        ( function-pointed-Π B C g)
        ( inv (preserves-point-pointed-map A B f)))) ∙
    ( ap
      ( tr
        ( fam-Pointed-Fam B C)
        ( inv (preserves-point-pointed-map A B f)))
      ( preserves-point-function-pointed-Π B C g))
```

### Composing pointed maps

```agda
module _
  {l1 l2 l3 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2) (C : Pointed-Type l3)
  where

  map-comp-pointed-map :
    B →∗ C → A →∗ B → type-Pointed-Type A → type-Pointed-Type C
  map-comp-pointed-map g f =
    map-pointed-map B C g ∘ map-pointed-map A B f

  preserves-point-comp-pointed-map :
    (g : B →∗ C) (f : A →∗ B) →
    (map-comp-pointed-map g f (point-Pointed-Type A)) ＝ point-Pointed-Type C
  preserves-point-comp-pointed-map g f =
    ( ap (map-pointed-map B C g) (preserves-point-pointed-map A B f)) ∙
    ( preserves-point-pointed-map B C g)

  comp-pointed-map : B →∗ C → A →∗ B → A →∗ C
  pr1 (comp-pointed-map g f) = map-comp-pointed-map g f
  pr2 (comp-pointed-map g f) = preserves-point-comp-pointed-map g f

  precomp-pointed-map : A →∗ B → B →∗ C → A →∗ C
  precomp-pointed-map f g = comp-pointed-map g f

_∘∗_ :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3} →
  B →∗ C → A →∗ B → A →∗ C
_∘∗_ {A = A} {B} {C} = comp-pointed-map A B C
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
