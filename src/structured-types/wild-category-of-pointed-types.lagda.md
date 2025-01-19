# The wild category of pointed types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.wild-category-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import globular-types.discrete-reflexive-globular-types
open import globular-types.globular-types
open import globular-types.large-globular-types
open import globular-types.large-reflexive-globular-types
open import globular-types.large-transitive-globular-types
open import globular-types.reflexive-globular-types
open import globular-types.transitive-globular-types

open import structured-types.pointed-2-homotopies
open import structured-types.pointed-dependent-functions
open import structured-types.pointed-families-of-types
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.uniform-pointed-homotopies

open import wild-category-theory.noncoherent-large-omega-precategories
open import wild-category-theory.noncoherent-omega-precategories
```

</details>

## Idea

The
{{#concept "wild category of pointed types" Agda=uniform-pointed-type-Noncoherent-Large-ω-Precategory Agda=pointed-type-Noncoherent-Large-ω-Precategory}}
consists of [pointed types](structured-types.pointed-types.md),
[pointed functions](structured-types.pointed-maps.md), and
[pointed homotopies](structured-types.pointed-homotopies.md).

We give two equivalent definitions: the first uses
[uniform pointed homotopies](structured-types.uniform-pointed-homotopies.md),
giving a uniform definition for all higher cells. However, uniform pointed
homotopies are not as workable directly as pointed homotopies, although the
types are equivalent. Therefore we give a second, nonuniform definition of the
wild category of pointed types where the 2-cells are pointed homotopies, the
3-cells are [pointed 2-homotopies](structured-types.pointed-2-homotopies.md) and
the higher cells are [identities](foundation-core.identity-types.md).

## Definitions

### The noncoherent large ω-precategory of pointed types, pointed maps, and uniform pointed homotopies

#### The large globular type of pointed types, pointed maps, and uniform pointed homotopies

```agda
uniform-pointed-Π-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A) →
  Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
0-cell-Globular-Type (uniform-pointed-Π-Globular-Type A B) =
  pointed-Π A B
1-cell-globular-type-Globular-Type (uniform-pointed-Π-Globular-Type A B) f g =
  uniform-pointed-Π-Globular-Type A (eq-value-Pointed-Fam f g)

uniform-pointed-map-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
uniform-pointed-map-Globular-Type A B =
  uniform-pointed-Π-Globular-Type A (constant-Pointed-Fam A B)

uniform-pointed-type-Large-Globular-Type :
  Large-Globular-Type lsuc (λ l1 l2 → l1 ⊔ l2)
0-cell-Large-Globular-Type
  uniform-pointed-type-Large-Globular-Type l =
  Pointed-Type l
1-cell-globular-type-Large-Globular-Type
  uniform-pointed-type-Large-Globular-Type =
  uniform-pointed-map-Globular-Type
```

#### Identity structure on the large globular type of pointed types, pointed maps, and uniform pointed homotopies

```agda
is-reflexive-uniform-pointed-Π-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A) →
  is-reflexive-Globular-Type (uniform-pointed-Π-Globular-Type A B)
is-reflexive-1-cell-is-reflexive-Globular-Type
  ( is-reflexive-uniform-pointed-Π-Globular-Type A B) =
  refl-uniform-pointed-htpy
is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type
  ( is-reflexive-uniform-pointed-Π-Globular-Type A B)
  { f}
  { g} =
  is-reflexive-uniform-pointed-Π-Globular-Type A (eq-value-Pointed-Fam f g)

is-reflexive-uniform-pointed-map-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  is-reflexive-Globular-Type (uniform-pointed-map-Globular-Type A B)
is-reflexive-uniform-pointed-map-Globular-Type A B =
  is-reflexive-uniform-pointed-Π-Globular-Type A (constant-Pointed-Fam A B)

id-structure-uniform-pointed-type-Large-Globular-Type :
  is-reflexive-Large-Globular-Type uniform-pointed-type-Large-Globular-Type
refl-1-cell-is-reflexive-Large-Globular-Type
  id-structure-uniform-pointed-type-Large-Globular-Type A =
  id-pointed-map
is-reflexive-1-cell-globular-type-is-reflexive-Large-Globular-Type
  id-structure-uniform-pointed-type-Large-Globular-Type =
  is-reflexive-uniform-pointed-map-Globular-Type _ _
```

#### Composition structure on the large globular type of pointed types, pointed maps, and uniform pointed homotopies

```agda
is-transitive-uniform-pointed-Π-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A) →
  is-transitive-Globular-Type (uniform-pointed-Π-Globular-Type A B)
comp-1-cell-is-transitive-Globular-Type
  ( is-transitive-uniform-pointed-Π-Globular-Type A B) {f} {g} {h} K H =
  concat-uniform-pointed-htpy {f = f} {g} {h} H K
is-transitive-1-cell-globular-type-is-transitive-Globular-Type
  ( is-transitive-uniform-pointed-Π-Globular-Type A B) {f} {g} =
  is-transitive-uniform-pointed-Π-Globular-Type A (eq-value-Pointed-Fam f g)

uniform-pointed-Π-Transitive-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A) →
  Transitive-Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
uniform-pointed-Π-Transitive-Globular-Type A B =
  make-Transitive-Globular-Type
    ( uniform-pointed-Π-Globular-Type A B)
    ( is-transitive-uniform-pointed-Π-Globular-Type A B)

is-transitive-uniform-pointed-map-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  is-transitive-Globular-Type (uniform-pointed-map-Globular-Type A B)
is-transitive-uniform-pointed-map-Globular-Type A B =
  is-transitive-uniform-pointed-Π-Globular-Type A (constant-Pointed-Fam A B)

uniform-pointed-map-Transitive-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Transitive-Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
uniform-pointed-map-Transitive-Globular-Type A B =
  uniform-pointed-Π-Transitive-Globular-Type A (constant-Pointed-Fam A B)

comp-structure-uniform-pointed-type-Large-Globular-Type :
  is-transitive-Large-Globular-Type uniform-pointed-type-Large-Globular-Type
comp-1-cell-is-transitive-Large-Globular-Type
  comp-structure-uniform-pointed-type-Large-Globular-Type g f =
  g ∘∗ f
is-transitive-1-cell-globular-type-is-transitive-Large-Globular-Type
  comp-structure-uniform-pointed-type-Large-Globular-Type =
  is-transitive-uniform-pointed-Π-Globular-Type _ _
```

#### The noncoherent large ω-precategory of pointed types, pointed maps, and uniform pointed homotopies

```agda
uniform-pointed-type-Noncoherent-Large-ω-Precategory :
  Noncoherent-Large-ω-Precategory lsuc (_⊔_)
large-globular-type-Noncoherent-Large-ω-Precategory
  uniform-pointed-type-Noncoherent-Large-ω-Precategory =
  uniform-pointed-type-Large-Globular-Type
id-structure-Noncoherent-Large-ω-Precategory
  uniform-pointed-type-Noncoherent-Large-ω-Precategory =
  id-structure-uniform-pointed-type-Large-Globular-Type
comp-structure-Noncoherent-Large-ω-Precategory
  uniform-pointed-type-Noncoherent-Large-ω-Precategory =
  comp-structure-uniform-pointed-type-Large-Globular-Type
```

### The noncoherent large ω-precategory of pointed types, pointed maps, and nonuniform homotopies

#### The large globular type of pointed types, pointed maps, and nonuniform pointed homotopies

```agda
pointed-htpy-Globular-Type :
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B) → Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
0-cell-Globular-Type (pointed-htpy-Globular-Type f g) = f ~∗ g
1-cell-globular-type-Globular-Type (pointed-htpy-Globular-Type f g) H K =
  globular-type-discrete-Reflexive-Globular-Type (pointed-2-htpy H K)

pointed-Π-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A) →
  Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
0-cell-Globular-Type
  ( pointed-Π-Globular-Type A B) =
  pointed-Π A B
1-cell-globular-type-Globular-Type
  ( pointed-Π-Globular-Type A B) =
  pointed-htpy-Globular-Type

pointed-map-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
pointed-map-Globular-Type A B =
  pointed-Π-Globular-Type A (constant-Pointed-Fam A B)

pointed-type-Large-Globular-Type :
  Large-Globular-Type lsuc (λ l1 l2 → l1 ⊔ l2)
0-cell-Large-Globular-Type pointed-type-Large-Globular-Type l =
  Pointed-Type l
1-cell-globular-type-Large-Globular-Type pointed-type-Large-Globular-Type =
  pointed-map-Globular-Type
```

#### Identity structure on the large globular type of nonpointed types, pointed maps, and uniform pointed homotopies

```agda
is-reflexive-pointed-htpy-Globular-Type :
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B) →
  is-reflexive-Globular-Type (pointed-htpy-Globular-Type f g)
is-reflexive-1-cell-is-reflexive-Globular-Type
  ( is-reflexive-pointed-htpy-Globular-Type f g) =
  refl-pointed-2-htpy
is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type
  ( is-reflexive-pointed-htpy-Globular-Type f g) =
  refl-discrete-Reflexive-Globular-Type

pointed-htpy-Reflexive-Globular-Type :
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B) → Reflexive-Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
globular-type-Reflexive-Globular-Type
  ( pointed-htpy-Reflexive-Globular-Type f g) =
  pointed-htpy-Globular-Type f g
refl-Reflexive-Globular-Type
  ( pointed-htpy-Reflexive-Globular-Type f g) =
  is-reflexive-pointed-htpy-Globular-Type f g

is-reflexive-pointed-Π-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A) →
  is-reflexive-Globular-Type (pointed-Π-Globular-Type A B)
is-reflexive-1-cell-is-reflexive-Globular-Type
  ( is-reflexive-pointed-Π-Globular-Type A B) =
  refl-pointed-htpy
is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type
  ( is-reflexive-pointed-Π-Globular-Type A B) =
  is-reflexive-pointed-htpy-Globular-Type _ _

pointed-Π-Reflexive-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A) →
  Reflexive-Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
globular-type-Reflexive-Globular-Type
  ( pointed-Π-Reflexive-Globular-Type A B) =
  pointed-Π-Globular-Type A B
refl-Reflexive-Globular-Type
  ( pointed-Π-Reflexive-Globular-Type A B) =
  is-reflexive-pointed-Π-Globular-Type A B

is-reflexive-pointed-map-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  is-reflexive-Globular-Type (pointed-map-Globular-Type A B)
is-reflexive-pointed-map-Globular-Type A B =
  is-reflexive-pointed-Π-Globular-Type A (constant-Pointed-Fam A B)

pointed-map-Reflexive-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Reflexive-Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
pointed-map-Reflexive-Globular-Type A B =
  pointed-Π-Reflexive-Globular-Type A (constant-Pointed-Fam A B)

is-reflexive-pointed-type-Large-Globular-Type :
  is-reflexive-Large-Globular-Type pointed-type-Large-Globular-Type
refl-1-cell-is-reflexive-Large-Globular-Type
  is-reflexive-pointed-type-Large-Globular-Type A = id-pointed-map
is-reflexive-1-cell-globular-type-is-reflexive-Large-Globular-Type
  is-reflexive-pointed-type-Large-Globular-Type =
  is-reflexive-pointed-map-Globular-Type _ _

pointed-type-Large-Reflexive-Globular-Type :
  Large-Reflexive-Globular-Type lsuc (_⊔_)
large-globular-type-Large-Reflexive-Globular-Type
  pointed-type-Large-Reflexive-Globular-Type =
  pointed-type-Large-Globular-Type
is-reflexive-Large-Reflexive-Globular-Type
  pointed-type-Large-Reflexive-Globular-Type =
  is-reflexive-pointed-type-Large-Globular-Type
```

#### Composition structure on the large globular type of nonpointed types, pointed maps, and uniform pointed homotopies

```agda
is-transitive-pointed-htpy-Globular-Type :
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B) →
  is-transitive-Globular-Type (pointed-htpy-Globular-Type f g)
comp-1-cell-is-transitive-Globular-Type
  ( is-transitive-pointed-htpy-Globular-Type f g) K H =
  concat-pointed-2-htpy H K
is-transitive-1-cell-globular-type-is-transitive-Globular-Type
  ( is-transitive-pointed-htpy-Globular-Type f g) =
  is-transitive-discrete-Reflexive-Globular-Type

is-transitive-pointed-Π-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A) →
  is-transitive-Globular-Type (pointed-Π-Globular-Type A B)
comp-1-cell-is-transitive-Globular-Type
  ( is-transitive-pointed-Π-Globular-Type A B) K H =
  concat-pointed-htpy H K
is-transitive-1-cell-globular-type-is-transitive-Globular-Type
  ( is-transitive-pointed-Π-Globular-Type A B) =
  is-transitive-pointed-htpy-Globular-Type _ _

is-transitive-pointed-map-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  is-transitive-Globular-Type (pointed-map-Globular-Type A B)
is-transitive-pointed-map-Globular-Type A B =
  is-transitive-pointed-Π-Globular-Type A (constant-Pointed-Fam A B)

is-transitive-pointed-type-Large-Globular-Type :
  is-transitive-Large-Globular-Type pointed-type-Large-Globular-Type
comp-1-cell-is-transitive-Large-Globular-Type
  is-transitive-pointed-type-Large-Globular-Type g f =
  g ∘∗ f
is-transitive-1-cell-globular-type-is-transitive-Large-Globular-Type
  is-transitive-pointed-type-Large-Globular-Type =
  is-transitive-pointed-map-Globular-Type _ _
```

#### The noncoherent large ω-precategory of pointed types, pointed maps, and nonuniform pointed homotopies

```agda
pointed-type-Noncoherent-Large-ω-Precategory :
  Noncoherent-Large-ω-Precategory lsuc (_⊔_)
large-globular-type-Noncoherent-Large-ω-Precategory
  pointed-type-Noncoherent-Large-ω-Precategory =
  pointed-type-Large-Globular-Type
id-structure-Noncoherent-Large-ω-Precategory
  pointed-type-Noncoherent-Large-ω-Precategory =
  is-reflexive-pointed-type-Large-Globular-Type
comp-structure-Noncoherent-Large-ω-Precategory
  pointed-type-Noncoherent-Large-ω-Precategory =
  is-transitive-pointed-type-Large-Globular-Type
```

## See also

- The categorical laws of pointed maps and pointed homotopies are proven in
  [pointed homotopies](structured-types.pointed-homotopies.md).
- The categorical laws of pointed maps and uniform pointed homotopies are proven
  in
  [uniform pointed homotopies](structured-types.uniform-pointed-homotopies.md).
