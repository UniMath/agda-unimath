# Finiteness of the type of connected components

```agda
module univalent-combinatorics.finitely-many-connected-components where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functoriality-set-truncation
open import foundation.mere-equivalences
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
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
  has-cardinality-Prop k (type-trunc-Set A)

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

### Empty types have finitely many connected components

```agda
has-finitely-many-connected-components-is-empty :
  {l : Level} {A : UU l} → is-empty A → has-finitely-many-connected-components A
has-finitely-many-connected-components-is-empty f =
  is-finite-is-empty (is-empty-trunc-Set f)
```

### Any `0`-connected type has finitely many connected components

```agda
has-finitely-many-connected-components-is-0-connected :
  {l : Level} {A : UU l} →
  is-0-connected A → has-finitely-many-connected-components A
has-finitely-many-connected-components-is-0-connected = is-finite-is-contr
```

### Sets with finitely many connected components are finite

```agda
is-finite-has-finitely-many-connected-components :
  {l : Level} {A : UU l} →
  is-set A → has-finitely-many-connected-components A → is-finite A
is-finite-has-finitely-many-connected-components H =
  is-finite-equiv' (equiv-unit-trunc-Set (_ , H))
```

## See also

- [Kuratowski finite sets](univalent-combinatorics.kuratowski-finite-sets.md)
