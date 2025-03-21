# The wild category of types

```agda
{-# OPTIONS --guardedness #-}

module foundation.wild-category-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.globular-type-of-functions
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

open import globular-types.globular-types
open import globular-types.large-globular-types
open import globular-types.large-reflexive-globular-types
open import globular-types.large-transitive-globular-types
open import globular-types.reflexive-globular-types
open import globular-types.transitive-globular-types

open import wild-category-theory.noncoherent-large-omega-precategories
open import wild-category-theory.noncoherent-omega-precategories
```

</details>

## Idea

The
{{#concept "wild category of types" Agda=Type-Noncoherent-Large-ω-Precategory}}
consists of types and [functions](foundation.dependent-function-types.md) and
[homotopies](foundation-core.homotopies.md).

## Definitions

### The large globular type of types

```agda
Type-Large-Globular-Type : Large-Globular-Type lsuc (_⊔_)
0-cell-Large-Globular-Type Type-Large-Globular-Type l =
  UU l
1-cell-globular-type-Large-Globular-Type Type-Large-Globular-Type A B =
  function-type-Globular-Type A B

is-reflexive-Type-Large-Globular-Type :
  is-reflexive-Large-Globular-Type Type-Large-Globular-Type
refl-1-cell-is-reflexive-Large-Globular-Type
  is-reflexive-Type-Large-Globular-Type X =
  id
is-reflexive-1-cell-globular-type-is-reflexive-Large-Globular-Type
  is-reflexive-Type-Large-Globular-Type =
  is-reflexive-function-type-Globular-Type

Type-Large-Reflexive-Globular-Type : Large-Reflexive-Globular-Type lsuc (_⊔_)
large-globular-type-Large-Reflexive-Globular-Type
  Type-Large-Reflexive-Globular-Type =
  Type-Large-Globular-Type
is-reflexive-Large-Reflexive-Globular-Type
  Type-Large-Reflexive-Globular-Type =
  is-reflexive-Type-Large-Globular-Type

is-transitive-Type-Large-Globular-Type :
  is-transitive-Large-Globular-Type Type-Large-Globular-Type
comp-1-cell-is-transitive-Large-Globular-Type
  is-transitive-Type-Large-Globular-Type g f =
  g ∘ f
is-transitive-1-cell-globular-type-is-transitive-Large-Globular-Type
  is-transitive-Type-Large-Globular-Type =
  is-transitive-function-type-Globular-Type

Type-Large-Transitive-Globular-Type : Large-Transitive-Globular-Type lsuc (_⊔_)
large-globular-type-Large-Transitive-Globular-Type
  Type-Large-Transitive-Globular-Type =
  Type-Large-Globular-Type
is-transitive-Large-Transitive-Globular-Type
  Type-Large-Transitive-Globular-Type =
  is-transitive-Type-Large-Globular-Type
```

### The noncoherent large ω-precategory of types

```agda
Type-Noncoherent-Large-ω-Precategory :
  Noncoherent-Large-ω-Precategory lsuc (_⊔_)
large-globular-type-Noncoherent-Large-ω-Precategory
  Type-Noncoherent-Large-ω-Precategory =
  Type-Large-Globular-Type
id-structure-Noncoherent-Large-ω-Precategory
  Type-Noncoherent-Large-ω-Precategory =
  is-reflexive-Type-Large-Globular-Type
comp-structure-Noncoherent-Large-ω-Precategory
  Type-Noncoherent-Large-ω-Precategory =
  is-transitive-Type-Large-Globular-Type
```
