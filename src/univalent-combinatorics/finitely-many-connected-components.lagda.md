# Finiteness of the type of connected components

```agda
module univalent-combinatorics.finitely-many-connected-components where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-set-truncation
open import foundation.mere-equivalences
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.set-truncations
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.distributivity-of-set-truncation-over-finite-products
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.retracts-of-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type is said to have
{{#concept "finitely many connected components"  Disambiguation="of a type" Agda=has-finitely-many-connected-components}}
if its [set truncation](foundation.set-truncations.md) is a
[finite type](univalent-combinatorics.finite-types.md).

## Definitions

### Types with finitely many connected components

```agda
has-finitely-many-connected-components-Prop : {l : Level} → UU l → Prop l
has-finitely-many-connected-components-Prop A =
  is-finite-Prop (type-trunc-Set A)

has-finitely-many-connected-components : {l : Level} → UU l → UU l
has-finitely-many-connected-components A =
  type-Prop (has-finitely-many-connected-components-Prop A)

is-prop-has-finitely-many-connected-components :
  {l : Level} {X : UU l} → is-prop (has-finitely-many-connected-components X)
is-prop-has-finitely-many-connected-components {X = X} =
  is-prop-type-Prop (has-finitely-many-connected-components-Prop X)

number-of-connected-components :
  {l : Level} {X : UU l} → has-finitely-many-connected-components X → ℕ
number-of-connected-components H = number-of-elements-is-finite H

mere-equiv-number-of-connected-components :
  {l : Level} {X : UU l} (H : has-finitely-many-connected-components X) →
  mere-equiv
    ( Fin (number-of-connected-components H))
    ( type-trunc-Set X)
mere-equiv-number-of-connected-components H =
  mere-equiv-is-finite H
```

### Types with a finite type of connected components of a specified cardinality

```agda
has-cardinality-connected-components-Prop : {l : Level} (k : ℕ) → UU l → Prop l
has-cardinality-connected-components-Prop k A =
  has-cardinality-ℕ-Prop k (type-trunc-Set A)

has-cardinality-connected-components : {l : Level} (k : ℕ) → UU l → UU l
has-cardinality-connected-components k A =
  type-Prop (has-cardinality-connected-components-Prop k A)
```

## Properties

### Having finitely many connected components is invariant under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  has-finitely-many-connected-components-equiv :
    has-finitely-many-connected-components A →
    has-finitely-many-connected-components B
  has-finitely-many-connected-components-equiv =
    is-finite-equiv (equiv-trunc-Set e)

  has-finitely-many-connected-components-equiv' :
    has-finitely-many-connected-components B →
    has-finitely-many-connected-components A
  has-finitely-many-connected-components-equiv' =
    is-finite-equiv' (equiv-trunc-Set e)
```

### Having finitely many connected components is invariant under retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (r : A retract-of B)
  where

  has-finitely-many-connected-components-retract :
    has-finitely-many-connected-components B →
    has-finitely-many-connected-components A
  has-finitely-many-connected-components-retract =
    is-finite-retract (retract-trunc-Set r)
```

### Empty types have finitely many connected components

```agda
has-finitely-many-connected-components-is-empty :
  {l : Level} {A : UU l} → is-empty A → has-finitely-many-connected-components A
has-finitely-many-connected-components-is-empty f =
  is-finite-is-empty (is-empty-trunc-Set f)

has-finitely-many-connected-components-empty :
  has-finitely-many-connected-components empty
has-finitely-many-connected-components-empty =
  has-finitely-many-connected-components-is-empty id
```

### Contractible types have finitely many connected components

```agda
has-finitely-many-connected-components-is-contr :
  {l : Level} {A : UU l} →
  is-contr A → has-finitely-many-connected-components A
has-finitely-many-connected-components-is-contr H =
  is-finite-is-contr (is-contr-trunc-Set H)

has-finitely-many-connected-components-unit :
  has-finitely-many-connected-components unit
has-finitely-many-connected-components-unit =
  has-finitely-many-connected-components-is-contr is-contr-unit
```

### Coproducts of types with finitely many connected components

```agda
has-finitely-many-connected-components-coproduct :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-finitely-many-connected-components A →
  has-finitely-many-connected-components B →
  has-finitely-many-connected-components (A + B)
has-finitely-many-connected-components-coproduct H K =
  is-finite-equiv'
    ( equiv-distributive-trunc-coproduct-Set _ _)
    ( is-finite-coproduct H K)
```

### Any `0`-connected type has finitely many connected components

```agda
has-finitely-many-connected-components-is-0-connected :
  {l : Level} {A : UU l} →
  is-0-connected A → has-finitely-many-connected-components A
has-finitely-many-connected-components-is-0-connected = is-finite-is-contr
```

### Finite types have finitely many connected components

```agda
has-finitely-many-connected-components-is-finite :
  {l : Level} {A : UU l} →
  is-finite A → has-finitely-many-connected-components A
has-finitely-many-connected-components-is-finite {A = A} H =
  is-finite-equiv (equiv-unit-trunc-Set (A , is-set-is-finite H)) H
```

### Sets with finitely many connected components are finite

```agda
is-finite-has-finitely-many-connected-components :
  {l : Level} {A : UU l} →
  is-set A → has-finitely-many-connected-components A → is-finite A
is-finite-has-finitely-many-connected-components H =
  is-finite-equiv' (equiv-unit-trunc-Set (_ , H))
```

### The type of all `n`-element types in `UU l` has finitely many connected components

```agda
has-finitely-many-connected-components-Type-With-Cardinality-ℕ :
  {l : Level} (n : ℕ) →
  has-finitely-many-connected-components (Type-With-Cardinality-ℕ l n)
has-finitely-many-connected-components-Type-With-Cardinality-ℕ n =
  has-finitely-many-connected-components-is-0-connected
    ( is-0-connected-Type-With-Cardinality-ℕ n)
```

### Finite products of types with finitely many connected components

```agda
has-finitely-many-connected-components-finite-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-finite A →
  ((a : A) → has-finitely-many-connected-components (B a)) →
  has-finitely-many-connected-components ((a : A) → B a)
has-finitely-many-connected-components-finite-Π {B = B} H K =
  is-finite-equiv'
    ( equiv-distributive-trunc-Π-is-finite-Set B H)
    ( is-finite-Π H K)
```

## See also

- [Kuratowski finite sets](univalent-combinatorics.kuratowski-finite-sets.md)
- [π-finite types](univalent-combinatorics.pi-finite-types.md)
- [Unbounded π-finite types](univalent-combinatorics.unbounded-pi-finite-types.md)
