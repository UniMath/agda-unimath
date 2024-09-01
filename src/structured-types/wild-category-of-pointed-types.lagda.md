# The wild category of pointed types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.wild-category-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.globular-types
open import structured-types.large-globular-types
open import structured-types.large-reflexive-globular-types
open import structured-types.large-transitive-globular-types
open import structured-types.pointed-dependent-functions
open import structured-types.pointed-families-of-types
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.reflexive-globular-types
open import structured-types.transitive-globular-types
open import structured-types.uniform-pointed-homotopies

open import wild-category-theory.noncoherent-large-wild-higher-precategories
open import wild-category-theory.noncoherent-wild-higher-precategories
```

</details>

## Idea

The
{{#concept "wild category of pointed types" Agda=Pointed-Pointed-Type-Noncoherent-Large-Wild-Higher-Precategory}}
consists of [pointed types](structured-types.pointed-types.md)
[pointed functions](structured-types.pointed-functions.md) and
[pointed homotopies](structured-types.pointed-homotopies.md).

## Definitions

### The globular structure on dependent pointed function types

```agda
globular-structure-pointed-Π :
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A} →
  globular-structure (l1 ⊔ l2) (pointed-Π A B)
globular-structure-pointed-Π =
  λ where
  .1-cell-globular-structure →
    uniform-pointed-htpy
  .globular-structure-1-cell-globular-structure f g →
    globular-structure-pointed-Π

is-reflexive-globular-structure-pointed-Π :
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A} →
  is-reflexive-globular-structure (globular-structure-pointed-Π {A = A} {B})
is-reflexive-globular-structure-pointed-Π =
  λ where
  .is-reflexive-1-cell-is-reflexive-globular-structure →
    refl-uniform-pointed-htpy
  .is-reflexive-globular-structure-1-cell-is-reflexive-globular-structure f g →
    is-reflexive-globular-structure-pointed-Π

is-transitive-globular-structure-pointed-Π :
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A} →
  is-transitive-globular-structure (globular-structure-pointed-Π {A = A} {B})
is-transitive-globular-structure-pointed-Π =
  λ where
  .comp-1-cell-is-transitive-globular-structure {f} {g} {h} H K →
    concat-uniform-pointed-htpy {f = f} {g} {h} K H
  .is-transitive-globular-structure-1-cell-is-transitive-globular-structure
    H K →
    is-transitive-globular-structure-pointed-Π
```

### The large globular structure on pointed types

```agda
large-globular-structure-Pointed-Type :
  large-globular-structure (_⊔_) Pointed-Type
large-globular-structure-Pointed-Type =
  λ where
  .1-cell-large-globular-structure X Y →
    (X →∗ Y)
  .globular-structure-1-cell-large-globular-structure X Y →
    globular-structure-pointed-Π

is-reflexive-large-globular-structure-Pointed-Type :
  is-reflexive-large-globular-structure large-globular-structure-Pointed-Type
is-reflexive-large-globular-structure-Pointed-Type =
  λ where
  .is-reflexive-1-cell-is-reflexive-large-globular-structure X →
    id-pointed-map
  .is-reflexive-globular-structure-1-cell-is-reflexive-large-globular-structure
    X Y →
    is-reflexive-globular-structure-pointed-Π

is-transitive-large-globular-structure-Pointed-Type :
  is-transitive-large-globular-structure large-globular-structure-Pointed-Type
is-transitive-large-globular-structure-Pointed-Type =
  λ where
  .comp-1-cell-is-transitive-large-globular-structure g f →
    g ∘∗ f
  .is-transitive-globular-structure-1-cell-is-transitive-large-globular-structure
    X Y →
    is-transitive-globular-structure-pointed-Π
```

### The noncoherent large wild higher precategory of types

```agda
Pointed-Type-Noncoherent-Large-Wild-Higher-Precategory :
  Noncoherent-Large-Wild-Higher-Precategory lsuc (_⊔_)
Pointed-Type-Noncoherent-Large-Wild-Higher-Precategory =
  λ where
  .obj-Noncoherent-Large-Wild-Higher-Precategory →
    Pointed-Type
  .hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory →
    large-globular-structure-Pointed-Type
  .id-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory →
    is-reflexive-large-globular-structure-Pointed-Type
  .comp-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory →
    is-transitive-large-globular-structure-Pointed-Type
```
