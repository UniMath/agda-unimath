# Kuratowski finite sets

```agda
module univalent-combinatorics.kuratowski-finite-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universe-levels

open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A {{#concept "Kuratowski finite set" Agda=Kuratowski-Finite-Set}} is a
[set](foundation-core.sets.md) `X` for which there exists a
[surjection](foundation.surjective-maps.md) into `X` from a standard finite
type. In other words, a Kuratowski finite set is a
[set-quotient](foundation.set-quotients.md) of a
[standard finite type](univalent-combinatorics.standard-finite-types.md).

## Definition

```agda
is-kuratowski-finite-set-Prop : {l : Level} → Set l → Prop l
is-kuratowski-finite-set-Prop X =
  exists-structure-Prop ℕ (λ n → Fin n ↠ type-Set X)

is-kuratowski-finite-set : {l : Level} → Set l → UU l
is-kuratowski-finite-set X = type-Prop (is-kuratowski-finite-set-Prop X)

Kuratowski-Finite-Set : (l : Level) → UU (lsuc l)
Kuratowski-Finite-Set l = Σ (Set l) is-kuratowski-finite-set

module _
  {l : Level} (X : Kuratowski-Finite-Set l)
  where

  set-Finite-Type-Kuratowski : Set l
  set-Finite-Type-Kuratowski = pr1 X

  type-Kuratowski-Finite-Set : UU l
  type-Kuratowski-Finite-Set = type-Set set-Finite-Type-Kuratowski

  is-set-type-Kuratowski-Finite-Set : is-set type-Kuratowski-Finite-Set
  is-set-type-Kuratowski-Finite-Set = is-set-type-Set set-Finite-Type-Kuratowski

  is-kuratowski-finite-set-Finite-Type-Kuratowski :
    is-kuratowski-finite-set set-Finite-Type-Kuratowski
  is-kuratowski-finite-set-Finite-Type-Kuratowski = pr2 X
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
    ( is-kuratowski-finite-set-Finite-Type-Kuratowski X)
    ( is-finite-Prop (type-Kuratowski-Finite-Set X))
    ( λ (n , f , s) → is-finite-codomain (is-finite-Fin n) s H)

has-decidable-equality-is-finite-type-Kuratowski-Finite-Set :
  {l : Level} (X : Kuratowski-Finite-Set l) →
  is-finite (type-Kuratowski-Finite-Set X) →
  has-decidable-equality (type-Kuratowski-Finite-Set X)
has-decidable-equality-is-finite-type-Kuratowski-Finite-Set X =
  has-decidable-equality-is-finite
```

### Kuratowski finite sets are Markovian

> This remains to be formalized. ([Markovian types](logic.markovian-types.md))

## See also

- [Finite types](univalent-combinatorics.finite-types.md)
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
