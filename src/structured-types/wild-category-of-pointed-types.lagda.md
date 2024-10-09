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

open import structured-types.globular-types
open import structured-types.large-globular-types
open import structured-types.large-reflexive-globular-types
open import structured-types.large-transitive-globular-types
open import structured-types.pointed-2-homotopies
open import structured-types.pointed-dependent-functions
open import structured-types.pointed-families-of-types
open import structured-types.pointed-homotopies
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
{{#concept "wild category of pointed types" Agda=uniform-Pointed-Type-Noncoherent-Large-Wild-Higher-Precategory Agda=Pointed-Type-Noncoherent-Large-Wild-Higher-Precategory}}
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

### The uniform definition of the wild category of pointed types

#### The uniform globular structure on dependent pointed function types

- The large globular type of pointed types, pointed maps, and uniform pointed homotopies

```agda
uniform-globular-structure-pointed-Π :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A) →
  globular-structure (l1 ⊔ l2) (pointed-Π A B)
1-cell-globular-structure
  ( uniform-globular-structure-pointed-Π A B) =
  uniform-pointed-htpy
globular-structure-1-cell-globular-structure
  ( uniform-globular-structure-pointed-Π A B) f g =
  uniform-globular-structure-pointed-Π _ _

uniform-pointed-Π-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A) →
  Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
uniform-pointed-Π-Globular-Type A B =
  make-Globular-Type (uniform-globular-structure-pointed-Π A B)

uniform-globular-structure-pointed-map :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  globular-structure (l1 ⊔ l2) (A →∗ B)
uniform-globular-structure-pointed-map A B =
  uniform-globular-structure-pointed-Π A (constant-Pointed-Fam A B)

uniform-pointed-map-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
uniform-pointed-map-Globular-Type A B =
  make-Globular-Type (uniform-globular-structure-pointed-map A B)

uniform-large-globular-structure-Pointed-Type :
  large-globular-structure (λ l1 l2 → l1 ⊔ l2) Pointed-Type
1-cell-large-globular-structure
  uniform-large-globular-structure-Pointed-Type = pointed-map
globular-structure-1-cell-large-globular-structure
  uniform-large-globular-structure-Pointed-Type =
  uniform-globular-structure-pointed-map

uniform-pointed-type-Large-Globular-Type :
  Large-Globular-Type lsuc (λ l1 l2 → l1 ⊔ l2)
uniform-pointed-type-Large-Globular-Type =
  make-Large-Globular-Type uniform-large-globular-structure-Pointed-Type
```

- Identity structure on the large globular type of uniform pointed types

```agda
is-reflexive-uniform-globular-structure-pointed-Π :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A) →
  is-reflexive-globular-structure
    ( uniform-globular-structure-pointed-Π A B)
is-reflexive-1-cell-is-reflexive-globular-structure
  ( is-reflexive-uniform-globular-structure-pointed-Π A B) =
  refl-uniform-pointed-htpy
is-reflexive-globular-structure-1-cell-is-reflexive-globular-structure
  ( is-reflexive-uniform-globular-structure-pointed-Π A B) f g =
  is-reflexive-uniform-globular-structure-pointed-Π _ _

is-reflexive-uniform-pointed-Π-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A) →
  is-reflexive-Globular-Type (uniform-pointed-Π-Globular-Type A B)
is-reflexive-uniform-pointed-Π-Globular-Type A B =
  is-reflexive-globular-type-is-reflexive-globular-structure
    ( is-reflexive-uniform-globular-structure-pointed-Π _ _)

is-reflexive-uniform-globular-structure-pointed-map :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  is-reflexive-globular-structure
    ( uniform-globular-structure-pointed-map A B)
is-reflexive-uniform-globular-structure-pointed-map A B =
  is-reflexive-uniform-globular-structure-pointed-Π A (constant-Pointed-Fam A B)

is-reflexive-uniform-pointed-map-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  is-reflexive-Globular-Type (uniform-pointed-map-Globular-Type A B)
is-reflexive-uniform-pointed-map-Globular-Type A B =
  is-reflexive-uniform-pointed-Π-Globular-Type A (constant-Pointed-Fam A B)

id-structure-uniform-pointed-type-Large-Globular-Type :
  is-reflexive-Large-Globular-Type uniform-pointed-type-Large-Globular-Type
refl-0-cell-is-reflexive-Large-Globular-Type
  id-structure-uniform-pointed-type-Large-Globular-Type A =
  id-pointed-map
is-reflexive-1-cell-globular-type-is-reflexive-Large-Globular-Type
  id-structure-uniform-pointed-type-Large-Globular-Type =
  is-reflexive-uniform-pointed-map-Globular-Type _ _
```

- Composition structure on the large globular type of uniform pointed types

```agda
is-transitive-uniform-globular-structure-pointed-Π :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A) →
  is-transitive-globular-structure
    ( uniform-globular-structure-pointed-Π A B)
comp-1-cell-is-transitive-globular-structure
  ( is-transitive-uniform-globular-structure-pointed-Π A B) {f} {g} {h} H K =
  concat-uniform-pointed-htpy {f = f} {g} {h} K H
is-transitive-globular-structure-1-cell-is-transitive-globular-structure
  ( is-transitive-uniform-globular-structure-pointed-Π A B) H K =
  is-transitive-uniform-globular-structure-pointed-Π _ _

is-transitive-uniform-pointed-Π-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A) →
  is-transitive-Globular-Type (uniform-pointed-Π-Globular-Type A B)
is-transitive-uniform-pointed-Π-Globular-Type A B =
  is-transitive-globular-type-is-transitive-globular-structure
    ( is-transitive-uniform-globular-structure-pointed-Π A B)

uniform-pointed-Π-Transitive-Globular-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A) →
  Transitive-Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
uniform-pointed-Π-Transitive-Globular-Type A B =
  make-Transitive-Globular-Type
    ( uniform-pointed-Π-Globular-Type A B)
    ( is-transitive-uniform-pointed-Π-Globular-Type A B)

is-transitive-uniform-globular-structure-pointed-map :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  is-transitive-globular-structure
    ( uniform-globular-structure-pointed-map A B)
is-transitive-uniform-globular-structure-pointed-map A B =
  is-transitive-uniform-globular-structure-pointed-Π A
    ( constant-Pointed-Fam A B)

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
comp-structure-uniform-pointed-type-Large-Globular-Type = {!!}
```

#### The uniform large globular structure on pointed types

-- ```agda
-- is-transitive-uniform-large-globular-structure-Pointed-Type :
--   is-transitive-large-globular-structure
--     uniform-large-globular-structure-Pointed-Type
-- is-transitive-uniform-large-globular-structure-Pointed-Type =
--   λ where
--   .comp-1-cell-is-transitive-large-globular-structure g f →
--     g ∘∗ f
--   .is-transitive-globular-structure-1-cell-is-transitive-large-globular-structure
--     X Y →
--     is-transitive-uniform-globular-structure-pointed-Π
-- ```

-- #### The uniform noncoherent large wild higher precategory of pointed types

-- ```agda
-- uniform-Pointed-Type-Noncoherent-Large-Wild-Higher-Precategory :
--   Noncoherent-Large-Wild-Higher-Precategory lsuc (_⊔_)
-- uniform-Pointed-Type-Noncoherent-Large-Wild-Higher-Precategory = {!!}

-- {-
--   λ where
--   .obj-Noncoherent-Large-Wild-Higher-Precategory →
--     Pointed-Type
--   .hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory →
--     uniform-large-globular-structure-Pointed-Type
--   .id-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory →
--     is-reflexive-uniform-large-globular-structure-Pointed-Type
--   .comp-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory →
--     is-transitive-uniform-large-globular-structure-Pointed-Type -}
-- ```

-- ### The nonuniform definition of the wild category of pointed types

-- #### The nonuniform globular structure on dependent pointed function types

-- ```agda
-- globular-structure-pointed-Π :
--   {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A} →
--   globular-structure (l1 ⊔ l2) (pointed-Π A B)
-- globular-structure-pointed-Π =
--   λ where
--   .1-cell-globular-structure →
--     pointed-htpy
--   .globular-structure-1-cell-globular-structure f g
--     .1-cell-globular-structure →
--     pointed-2-htpy
--   .globular-structure-1-cell-globular-structure f g
--     .globular-structure-1-cell-globular-structure H K →
--       globular-structure-Id (pointed-2-htpy H K)

-- is-reflexive-globular-structure-pointed-Π :
--   {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A} →
--   is-reflexive-globular-structure (globular-structure-pointed-Π {A = A} {B})
-- is-reflexive-globular-structure-pointed-Π =
--   λ where
--   .is-reflexive-1-cell-is-reflexive-globular-structure →
--     refl-pointed-htpy
--   .is-reflexive-globular-structure-1-cell-is-reflexive-globular-structure f g
--     .is-reflexive-1-cell-is-reflexive-globular-structure →
--       refl-pointed-2-htpy
--   .is-reflexive-globular-structure-1-cell-is-reflexive-globular-structure f g
--     .is-reflexive-globular-structure-1-cell-is-reflexive-globular-structure
--       H K →
--       is-reflexive-globular-structure-Id (pointed-2-htpy H K)

-- is-transitive-globular-structure-pointed-Π :
--   {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A} →
--   is-transitive-globular-structure (globular-structure-pointed-Π {A = A} {B})
-- is-transitive-globular-structure-pointed-Π =
--   λ where
--   .comp-1-cell-is-transitive-globular-structure {f} {g} {h} H K →
--     concat-pointed-htpy {f = f} {g} {h} K H
--   .is-transitive-globular-structure-1-cell-is-transitive-globular-structure H K
--     .comp-1-cell-is-transitive-globular-structure α β →
--     concat-pointed-2-htpy β α
--   .is-transitive-globular-structure-1-cell-is-transitive-globular-structure H K
--     .is-transitive-globular-structure-1-cell-is-transitive-globular-structure
--       α β →
--       is-transitive-globular-structure-Id (pointed-2-htpy α β)
-- ```

-- #### The nonuniform large globular structure on pointed types

-- ```agda
-- large-globular-structure-Pointed-Type :
--   large-globular-structure (_⊔_) Pointed-Type
-- large-globular-structure-Pointed-Type =
--   λ where
--   .1-cell-large-globular-structure X Y →
--     (X →∗ Y)
--   .globular-structure-1-cell-large-globular-structure X Y →
--     globular-structure-pointed-Π

-- is-reflexive-large-globular-structure-Pointed-Type :
--   is-reflexive-large-globular-structure large-globular-structure-Pointed-Type
-- is-reflexive-large-globular-structure-Pointed-Type =
--   λ where
--   .is-reflexive-1-cell-is-reflexive-large-globular-structure X →
--     id-pointed-map
--   .is-reflexive-globular-structure-1-cell-is-reflexive-large-globular-structure
--     X Y →
--     is-reflexive-globular-structure-pointed-Π

-- is-transitive-large-globular-structure-Pointed-Type :
--   is-transitive-large-globular-structure large-globular-structure-Pointed-Type
-- is-transitive-large-globular-structure-Pointed-Type =
--   λ where
--   .comp-1-cell-is-transitive-large-globular-structure g f →
--     g ∘∗ f
--   .is-transitive-globular-structure-1-cell-is-transitive-large-globular-structure
--     X Y →
--     is-transitive-globular-structure-pointed-Π
-- ```

-- #### The nonuniform noncoherent large wild higher precategory of pointed types

-- ```agda
-- Pointed-Type-Noncoherent-Large-Wild-Higher-Precategory :
--   Noncoherent-Large-Wild-Higher-Precategory lsuc (_⊔_)
-- Pointed-Type-Noncoherent-Large-Wild-Higher-Precategory = {!!}
-- {-
--   λ where
--   .obj-Noncoherent-Large-Wild-Higher-Precategory →
--     Pointed-Type
--   .hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory →
--     large-globular-structure-Pointed-Type
--   .id-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory →
--     is-reflexive-large-globular-structure-Pointed-Type
--   .comp-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory →
--     is-transitive-large-globular-structure-Pointed-Type -}
-- ```

-- ## Properties

-- ### The left unit law for the identity pointed map

-- ```agda
-- module _
--   {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
--   where

--   left-unit-law-id-pointed-map :
--     (f : A →∗ B) → id-pointed-map ∘∗ f ~∗ f
--   pr1 (left-unit-law-id-pointed-map f) = refl-htpy
--   pr2 (left-unit-law-id-pointed-map f) = right-unit ∙ ap-id (pr2 f)
-- ```

-- ### The right unit law for the identity pointed map

-- ```agda
-- module _
--   {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
--   where

--   right-unit-law-id-pointed-map :
--     (f : A →∗ B) → f ∘∗ id-pointed-map ~∗ f
--   right-unit-law-id-pointed-map = refl-pointed-htpy
-- ```
