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

A pointed map from a pointed type `A` to a pointed type `B` is a base point preserving function from `A` to `B`.

## Definitions

### Pointed maps

```agda
module _
  {l1 l2 : Level}
  where

  _→*_ : Pointed-Type l1 → Pointed-Type l2 → UU (l1 ⊔ l2)
  A →* B = pointed-Π A (constant-Pointed-Fam A B)

  constant-pointed-map : (A : Pointed-Type l1) (B : Pointed-Type l2) → A →* B
  pr1 (constant-pointed-map A B) =
    const (type-Pointed-Type A) (type-Pointed-Type B) (pt-Pointed-Type B)
  pr2 (constant-pointed-map A B) = refl

  [_→*_] : Pointed-Type l1 → Pointed-Type l2 → Pointed-Type (l1 ⊔ l2)
  pr1 [ A →* B ] = A →* B
  pr2 [ A →* B ] = constant-pointed-map A B

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  map-pointed-map : A →* B → type-Pointed-Type A → type-Pointed-Type B
  map-pointed-map f = pr1 f

  preserves-point-pointed-map :
    (f : A →* B) →
    map-pointed-map f (pt-Pointed-Type A) ＝ pt-Pointed-Type B
  preserves-point-pointed-map f = pr2 f
```

### Precomposing pointed pointed maps

```agda
module _
  {l1 l2 l3 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  (C : Pointed-Fam l3 B) (f : A →* B)
  where

  precomp-Pointed-Fam : Pointed-Fam l3 A
  precomp-Pointed-Fam =
    pair
      ( fam-Pointed-Fam B C ∘ map-pointed-map A B f)
      ( tr
        ( fam-Pointed-Fam B C)
        ( inv (preserves-point-pointed-map A B f))
        ( pt-Pointed-Fam B C))

  precomp-pointed-Π : pointed-Π B C → pointed-Π A precomp-Pointed-Fam
  precomp-pointed-Π g =
    pair
      ( λ x → function-pointed-Π B C g (map-pointed-map A B f x))
      ( ( inv
          ( apd
            ( function-pointed-Π B C g)
            ( inv (preserves-point-pointed-map A B f)))) ∙
        ( ap
          ( tr
            ( fam-Pointed-Fam B C)
            ( inv (preserves-point-pointed-map A B f)))
          ( preserves-point-function-pointed-Π B C g)))
```

### Composing pointed maps

```agda
module _
  {l1 l2 l3 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  (C : Pointed-Type l3)
  where

  map-comp-pointed-map :
    B →* C → A →* B → (type-Pointed-Type A) → (type-Pointed-Type C)
  map-comp-pointed-map g f =
    map-pointed-map B C g ∘ map-pointed-map A B f

  preserves-point-comp-pointed-map :
    (g : B →* C) (f : A →* B) →
    (map-comp-pointed-map g f (pt-Pointed-Type A)) ＝ pt-Pointed-Type C
  preserves-point-comp-pointed-map g f =
    ( ap (map-pointed-map B C g) (preserves-point-pointed-map A B f)) ∙
    ( preserves-point-pointed-map B C g)

  comp-pointed-map : B →* C → A →* B → A →* C
  pr1 (comp-pointed-map g f) = map-comp-pointed-map g f
  pr2 (comp-pointed-map g f) = preserves-point-comp-pointed-map g f

  precomp-pointed-map : A →* B → B →* C → A →* C
  precomp-pointed-map f g = comp-pointed-map g f
```

### The identity pointed map

```agda
module _
  {l1 : Level} {A : Pointed-Type l1}
  where

  id-pointed-map : A →* A
  id-pointed-map = pair id refl
```
