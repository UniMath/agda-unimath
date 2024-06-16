# The wild category of types

```agda
{-# OPTIONS --guardedness #-}

module foundation.wild-category-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.isomorphisms-of-sets
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types

open import structured-types.globular-types
open import structured-types.large-globular-types
open import structured-types.large-reflexive-globular-types
open import structured-types.large-transitive-globular-types
open import structured-types.reflexive-globular-types
open import structured-types.transitive-globular-types

open import wild-category-theory.isomorphisms-in-noncoherent-large-wild-higher-precategories
open import wild-category-theory.isomorphisms-in-noncoherent-wild-higher-precategories
open import wild-category-theory.noncoherent-large-wild-higher-precategories
open import wild-category-theory.noncoherent-wild-higher-precategories
```

</details>

## Idea

The
{{#concept "wild category of types" Agda=Type-Noncoherent-Large-Wild-Higher-Precategory}}
consists of types and functions and homotopies.

## Definitions

### The globular structure on dependent function types

```agda
globular-structure-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  globular-structure (l1 ⊔ l2) ((x : A) → B x)
globular-structure-Π =
  λ where
  .1-cell-globular-structure → _~_
  .globular-structure-1-cell-globular-structure f g → globular-structure-Π

is-reflexive-globular-structure-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-reflexive-globular-structure (globular-structure-Π {A = A} {B})
is-reflexive-globular-structure-Π =
  λ where
  .is-reflexive-1-cell-is-reflexive-globular-structure f → refl-htpy
  .is-reflexive-globular-structure-1-cell-is-reflexive-globular-structure f g →
    is-reflexive-globular-structure-Π

is-transitive-globular-structure-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-transitive-globular-structure (globular-structure-Π {A = A} {B})
is-transitive-globular-structure-Π =
  λ where
  .comp-1-cell-is-transitive-globular-structure H K → K ∙h H
  .is-transitive-globular-structure-1-cell-is-transitive-globular-structure
    H K →
    is-transitive-globular-structure-Π
```

### The large globular structure on types

```agda
large-globular-structure-Type : large-globular-structure (_⊔_) (λ l → UU l)
large-globular-structure-Type =
  λ where
  .1-cell-large-globular-structure X Y → (X → Y)
  .globular-structure-1-cell-large-globular-structure X Y → globular-structure-Π

is-reflexive-large-globular-structure-Type :
  is-reflexive-large-globular-structure large-globular-structure-Type
is-reflexive-large-globular-structure-Type =
  λ where
  .is-reflexive-1-cell-is-reflexive-large-globular-structure X → id
  .is-reflexive-globular-structure-1-cell-is-reflexive-large-globular-structure
    X Y →
    is-reflexive-globular-structure-Π

is-transitive-large-globular-structure-Type :
  is-transitive-large-globular-structure large-globular-structure-Type
is-transitive-large-globular-structure-Type =
  λ where
  .comp-1-cell-is-transitive-large-globular-structure g f → g ∘ f
  .is-transitive-globular-structure-1-cell-is-transitive-large-globular-structure
    X Y →
    is-transitive-globular-structure-Π
```

### The noncoherent large wild higher precategory of types

```agda
Type-Noncoherent-Large-Wild-Higher-Precategory :
  Noncoherent-Large-Wild-Higher-Precategory lsuc (_⊔_)
Type-Noncoherent-Large-Wild-Higher-Precategory =
  λ where
  .obj-Noncoherent-Large-Wild-Higher-Precategory l →
    UU l
  .hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory →
    large-globular-structure-Type
  .id-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory →
    is-reflexive-large-globular-structure-Type
  .comp-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory →
    is-transitive-large-globular-structure-Type
```
