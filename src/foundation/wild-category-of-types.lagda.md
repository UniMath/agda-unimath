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

### The globular type of dependent function types

```agda
dependent-function-type-Globular-Type :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
0-cell-Globular-Type (dependent-function-type-Globular-Type A B) =
  (x : A) → B x
1-cell-globular-type-Globular-Type
  ( dependent-function-type-Globular-Type A B) f g =
  dependent-function-type-Globular-Type A (eq-value f g)

globular-structure-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  globular-structure (l1 ⊔ l2) ((x : A) → B x)
globular-structure-Π {A = A} {B = B} =
  globular-structure-0-cell-Globular-Type
    ( dependent-function-type-Globular-Type A B)

is-reflexive-dependent-function-type-Globular-Type :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-reflexive-Globular-Type (dependent-function-type-Globular-Type A B)
is-reflexive-1-cell-is-reflexive-Globular-Type
  is-reflexive-dependent-function-type-Globular-Type f =
  refl-htpy
is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type
  is-reflexive-dependent-function-type-Globular-Type =
  is-reflexive-dependent-function-type-Globular-Type

is-transitive-dependent-function-type-Globular-Type :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-transitive-Globular-Type (dependent-function-type-Globular-Type A B)
comp-1-cell-is-transitive-Globular-Type
  is-transitive-dependent-function-type-Globular-Type K H =
  H ∙h K
is-transitive-1-cell-globular-type-is-transitive-Globular-Type
  is-transitive-dependent-function-type-Globular-Type =
  is-transitive-dependent-function-type-Globular-Type
```

### The globular type of function types

```agda
function-type-Globular-Type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
function-type-Globular-Type A B =
  dependent-function-type-Globular-Type A (λ _ → B)

globular-structure-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → globular-structure (l1 ⊔ l2) (A → B)
globular-structure-function-type = globular-structure-Π

is-reflexive-function-type-Globular-Type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-reflexive-Globular-Type (function-type-Globular-Type A B)
is-reflexive-function-type-Globular-Type {l1} {l2} {A} {B} =
  is-reflexive-dependent-function-type-Globular-Type

is-transitive-function-type-Globular-Type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-transitive-Globular-Type (function-type-Globular-Type A B)
is-transitive-function-type-Globular-Type =
  is-transitive-dependent-function-type-Globular-Type
```

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
```

### The noncoherent large wild higher precategory of types

```agda
Type-Noncoherent-Large-Wild-Higher-Precategory :
  Noncoherent-Large-Wild-Higher-Precategory lsuc (_⊔_)
large-globular-type-Noncoherent-Large-Wild-Higher-Precategory
  Type-Noncoherent-Large-Wild-Higher-Precategory =
  Type-Large-Globular-Type
id-structure-Noncoherent-Large-Wild-Higher-Precategory
  Type-Noncoherent-Large-Wild-Higher-Precategory =
  is-reflexive-Type-Large-Globular-Type
comp-structure-Noncoherent-Large-Wild-Higher-Precategory
  Type-Noncoherent-Large-Wild-Higher-Precategory =
  is-transitive-Type-Large-Globular-Type
```
