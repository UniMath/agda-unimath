# Noncoherent wild (∞,∞)-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.noncoherent-wild-infinity-infinity-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.action-on-identifications-binary-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels

open import structured-types.globular-types
open import structured-types.reflexive-globular-types
open import structured-types.transitive-globular-types
```

</details>

## Idea

A
{{#concept "noncoherent wild $(∞,∞)$-precategory" Agda=Noncoherent-Wild-⟨∞,∞⟩-Precategory}}
is a [reflexive](structured-types.reflexive-globular-types.md) and
[transitive](structured-types.transitive-globular-types.md)
[globular type](structured-types.globular-types.md). We call the 0-cells the
_objects_, the 1-cells the _morphisms_ and the higher cells the _$n$-morphisms_.
The reflexivities are called the _identity morphisms_, and the transitivity
operations are branded as _composition of morphisms_.

## Definitions

### Noncoherent wild $(∞,∞)$-precategories

```agda
Noncoherent-Wild-⟨∞,∞⟩-Precategory : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2 =
  Σ ( UU l1)
    ( λ obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory →
      Σ ( globular-structure l2 obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory)
        ( λ hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory →
          ( is-reflexive-globular-structure
            ( hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory)) ×
          ( is-transitive-globular-structure
            ( hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory))))

make-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
  {l1 l2 : Level} →
  (obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory : UU l1)
  (hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    globular-structure l2 obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory) →
  ( is-reflexive-globular-structure
    hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory) →
  ( is-transitive-globular-structure
    hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory) →
  Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2
make-Noncoherent-Wild-⟨∞,∞⟩-Precategory obj hom id comp =
  ( obj , hom , id , comp)

{-# INLINE make-Noncoherent-Wild-⟨∞,∞⟩-Precategory #-}

module _
  {l1 l2 : Level} (𝒞 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2)
  where

  obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory : UU l1
  obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory = pr1 𝒞

  hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    globular-structure l2 obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory
  hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory = pr1 (pr2 𝒞)

  id-hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    is-reflexive-globular-structure
      ( hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory)
  id-hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    pr1 (pr2 (pr2 𝒞))

  comp-hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    is-transitive-globular-structure
      ( hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory)
  comp-hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    pr2 (pr2 (pr2 𝒞))

  globular-type-Noncoherent-Wild-⟨∞,∞⟩-Precategory : Globular-Type l1 l2
  pr1 globular-type-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory
  pr2 globular-type-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory
```

We record some common projections for noncoherent wild $(∞,∞)$-precategories.

```agda
  hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory →
    obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory →
    UU l2
  hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    1-cell-globular-structure
      ( hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  id-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory} →
    hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory x x
  id-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    refl-1-cell-is-reflexive-globular-structure
      ( id-hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  comp-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y z : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory} →
    hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory y z →
    hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory x y →
    hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory x z
  comp-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    comp-1-cell-is-transitive-globular-structure
      ( comp-hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  hom-globular-type-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    (x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory) →
    Globular-Type l2 l2
  pr1 (hom-globular-type-Noncoherent-Wild-⟨∞,∞⟩-Precategory x y) =
    hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory x y
  pr2 (hom-globular-type-Noncoherent-Wild-⟨∞,∞⟩-Precategory x y) =
    globular-structure-1-cell-globular-structure
      ( hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory)
      ( x)
      ( y)

  hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    (x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory) →
    Noncoherent-Wild-⟨∞,∞⟩-Precategory l2 l2
  hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Wild-⟨∞,∞⟩-Precategory
    x y =
    make-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory x y)
      ( globular-structure-1-cell-globular-structure
        ( hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory)
        ( x)
        ( y))
      ( is-reflexive-globular-structure-1-cell-is-reflexive-globular-structure
        ( id-hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory)
        ( x)
        ( y))
      ( is-transitive-globular-structure-1-cell-is-transitive-globular-structure
        ( comp-hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory)
        ( x)
        ( y))
```

```agda
  2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory} →
    hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory x y →
    hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory x y →
    UU l2
  2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    2-cell-globular-structure
      ( hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  id-2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory}
    {f : hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory x y} →
    2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory f f
  id-2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    refl-2-cell-is-reflexive-globular-structure
      ( id-hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  comp-2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory}
    {f g h : hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory x y} →
    2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory g h →
    2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory f g →
    2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory f h
  comp-2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    comp-2-cell-is-transitive-globular-structure
      ( comp-hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory)
```

```agda
  3-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory}
    {f g : hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory x y} →
    2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory f g →
    2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory f g →
    UU l2
  3-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    3-cell-globular-structure
      ( hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  id-3-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory}
    {f g : hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory x y}
    {H : 2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory f g} →
    3-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory H H
  id-3-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    refl-3-cell-is-reflexive-globular-structure
      ( id-hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  comp-3-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory}
    {f g : hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory x y}
    {H K L : 2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory f g} →
    3-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory K L →
    3-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory H K →
    3-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory H L
  comp-3-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    comp-3-cell-is-transitive-globular-structure
      ( comp-hom-globular-structure-Noncoherent-Wild-⟨∞,∞⟩-Precategory)
```
