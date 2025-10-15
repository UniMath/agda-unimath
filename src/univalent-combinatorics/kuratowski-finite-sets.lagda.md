# Kuratowski finite sets

```agda
module univalent-combinatorics.kuratowski-finite-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universe-levels

open import set-theory.cardinalities
open import set-theory.inequality-cardinalities

open import univalent-combinatorics.dedekind-finite-sets
open import univalent-combinatorics.dedekind-finite-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-enumerable-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.subfinite-types
open import univalent-combinatorics.subfinitely-enumerable-types
```

</details>

## Idea

A {{#concept "Kuratowski finite set" Agda=Kuratowski-Finite-Set}} is a
[set](foundation-core.sets.md) `X` for which there
[exists](foundation.existential-quantification.md) a
[surjection](foundation.surjective-maps.md) into `X` from a
[standard finite type](univalent-combinatorics.standard-finite-types.md). In
other words, a Kuratowski finite set is a
[set-quotient](foundation.set-quotients.md) of a standard finite type.

## Definition

```agda
is-kuratowski-finite-prop-Set : {l : Level} → Set l → Prop l
is-kuratowski-finite-prop-Set X =
  exists-structure-Prop ℕ (λ n → Fin n ↠ type-Set X)

is-kuratowski-finite-Set : {l : Level} → Set l → UU l
is-kuratowski-finite-Set X = type-Prop (is-kuratowski-finite-prop-Set X)

Kuratowski-Finite-Set : (l : Level) → UU (lsuc l)
Kuratowski-Finite-Set l = Σ (Set l) is-kuratowski-finite-Set

module _
  {l : Level} (X : Kuratowski-Finite-Set l)
  where

  set-Kuratowski-Finite-Set : Set l
  set-Kuratowski-Finite-Set = pr1 X

  type-Kuratowski-Finite-Set : UU l
  type-Kuratowski-Finite-Set = type-Set set-Kuratowski-Finite-Set

  is-set-type-Kuratowski-Finite-Set : is-set type-Kuratowski-Finite-Set
  is-set-type-Kuratowski-Finite-Set = is-set-type-Set set-Kuratowski-Finite-Set

  is-kuratowski-finite-Kuratowski-Finite-Set :
    is-kuratowski-finite-Set set-Kuratowski-Finite-Set
  is-kuratowski-finite-Kuratowski-Finite-Set = pr2 X
```

## Properties

### A Kuratowski finite set is finite if and only if it has decidable equality

```agda
is-finite-has-decidable-equality-type-Kuratowski-Finite-Set :
  {l : Level} (X : Kuratowski-Finite-Set l) →
  has-decidable-equality (type-Kuratowski-Finite-Set X) →
  is-finite (type-Kuratowski-Finite-Set X)
is-finite-has-decidable-equality-type-Kuratowski-Finite-Set X H =
  apply-universal-property-trunc-Prop
    ( is-kuratowski-finite-Kuratowski-Finite-Set X)
    ( is-finite-Prop (type-Kuratowski-Finite-Set X))
    ( λ (n , f , s) → is-finite-codomain (is-finite-Fin n) s H)

has-decidable-equality-is-Kuratowski-Finite-Set-Finite-Set :
  {l : Level} (X : Kuratowski-Finite-Set l) →
  is-finite (type-Kuratowski-Finite-Set X) →
  has-decidable-equality (type-Kuratowski-Finite-Set X)
has-decidable-equality-is-Kuratowski-Finite-Set-Finite-Set X =
  has-decidable-equality-is-finite
```

### Kuratowski finite sets are Markovian

> This remains to be formalized. ([Markovian types](logic.markovian-types.md))

### Kuratowski finite sets are subfinitely enumerable

```agda
module _
  {l : Level} (X : Kuratowski-Finite-Set l)
  where

  is-subfinitely-enumerable-type-Kuratowski-Finite-Set :
    is-subfinitely-enumerable lzero (type-Kuratowski-Finite-Set X)
  is-subfinitely-enumerable-type-Kuratowski-Finite-Set =
    is-subfinitely-enumerable-is-finitely-enumerable
      ( is-kuratowski-finite-Kuratowski-Finite-Set X)

  subfinitely-enumerable-type-Kuratowski-Finite-Set :
    Subfinitely-Enumerable-Type l lzero
  subfinitely-enumerable-type-Kuratowski-Finite-Set =
    ( type-Kuratowski-Finite-Set X ,
      is-subfinitely-enumerable-type-Kuratowski-Finite-Set)
```

### Kuratowski finite sets are Dedekind finite

```agda
module _
  {l : Level} (X : Kuratowski-Finite-Set l)
  where

  is-dedekind-finite-type-Kuratowski-Finite-Set :
    is-dedekind-finite (type-Kuratowski-Finite-Set X)
  is-dedekind-finite-type-Kuratowski-Finite-Set =
    is-dedekind-finite-type-Subfinitely-Enumerable-Type
      ( subfinitely-enumerable-type-Kuratowski-Finite-Set X)

  dedekind-finite-type-Kuratowski-Finite-Set : Dedekind-Finite-Type l
  dedekind-finite-type-Kuratowski-Finite-Set =
    type-Kuratowski-Finite-Set X , is-dedekind-finite-type-Kuratowski-Finite-Set
```

### The Cantor–Schröder–Bernstein theorem for Kuratowski finite sets

If two Kuratowski finite sets `X` and `Y` mutually embed, `X ↪ Y` and `Y ↪ X`,
then `X ≃ Y`.

```agda
module _
  {l1 l2 : Level} (X : Kuratowski-Finite-Set l1) (Y : Kuratowski-Finite-Set l2)
  where

  Cantor-Schröder-Bernstein-Kuratowski-Finite-Set :
    (type-Kuratowski-Finite-Set X ↪ type-Kuratowski-Finite-Set Y) →
    (type-Kuratowski-Finite-Set Y ↪ type-Kuratowski-Finite-Set X) →
    type-Kuratowski-Finite-Set X ≃ type-Kuratowski-Finite-Set Y
  Cantor-Schröder-Bernstein-Kuratowski-Finite-Set =
    Cantor-Schröder-Bernstein-Dedekind-Finite-Type
      ( dedekind-finite-type-Kuratowski-Finite-Set X)
      ( dedekind-finite-type-Kuratowski-Finite-Set Y)
```

### Antisymmetry of inequality of cardinality of Kuratowski finite sets

```agda
cardinality-Kuratowski-Finite-Set :
  {l : Level} → Kuratowski-Finite-Set l → Cardinal l
cardinality-Kuratowski-Finite-Set X =
  cardinality (set-Kuratowski-Finite-Set X)

module _
  {l : Level} (X Y : Kuratowski-Finite-Set l)
  where

  antisymmetric-leq-cardinality-Kuratowski-Finite-Set :
    leq-cardinality
      ( set-Kuratowski-Finite-Set X)
      ( set-Kuratowski-Finite-Set Y) →
    leq-cardinality
      ( set-Kuratowski-Finite-Set Y)
      ( set-Kuratowski-Finite-Set X) →
    cardinality-Kuratowski-Finite-Set X ＝
    cardinality-Kuratowski-Finite-Set Y
  antisymmetric-leq-cardinality-Kuratowski-Finite-Set p q =
    eq-mere-equiv-cardinality
      ( set-Kuratowski-Finite-Set X)
      ( set-Kuratowski-Finite-Set Y)
      ( map-binary-trunc-Prop
        ( Cantor-Schröder-Bernstein-Kuratowski-Finite-Set X Y)
        ( inv-unit-leq-cardinality
          ( set-Kuratowski-Finite-Set X)
          ( set-Kuratowski-Finite-Set Y)
          ( p))
        ( inv-unit-leq-cardinality
          ( set-Kuratowski-Finite-Set Y)
          ( set-Kuratowski-Finite-Set X)
          ( q)))
```

## See also

- [Finite types](univalent-combinatorics.finite-types.md)
- [Finitely enumerable types](univalent-combinatorics.finitely-enumerable-types.md)
- [Subfinitely enumerable types](univalent-combinatorics.subfinitely-enumerable-types.md)
- [Dedekind finite sets](univalent-combinatorics.dedekind-finite-sets.md)
- In
  [`univalent-combinatorics.surjective-maps`](univalent-combinatorics.surjective-maps.md)
  it is shown that if a Kuratowski finite set has decidable equality then it is
  finite.

## External links

- [Finiteness in Sheaf Topoi](https://grossack.site/2024/08/19/finiteness-in-sheaf-topoi),
  blog post by Chris Grossack
- [`Fin.Kuratowski`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Fin.Kuratowski.html)
  at TypeTopology
- [finite set](https://ncatlab.org/nlab/show/finite+set) at $n$Lab
- [finite object](https://ncatlab.org/nlab/show/finite+object) at $n$Lab
- [Finite set](https://en.wikipedia.org/wiki/Finite_set) at Wikipedia
