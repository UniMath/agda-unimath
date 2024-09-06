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

A {{#concept "Kuratowski finite set" agda=𝔽-Kuratowski}} is a
[set](foundation-core.sets.md) `X` for which there exists a
[surjection](foundation.surjective-maps.md) into `X` from a standard finite
type. In other words, the Kuratowski finite set are the
[set-quotient](foundation.set-quotients.md) of a
[standard finite type](univalent-combinatorics.standard-finite-types.md).

## Definition

```agda
is-kuratowski-finite-set-Prop : {l : Level} → Set l → Prop l
is-kuratowski-finite-set-Prop X =
  exists-structure-Prop ℕ (λ n → Fin n ↠ type-Set X)

is-kuratowski-finite-set : {l : Level} → Set l → UU l
is-kuratowski-finite-set X = type-Prop (is-kuratowski-finite-set-Prop X)

𝔽-Kuratowski : (l : Level) → UU (lsuc l)
𝔽-Kuratowski l = Σ (Set l) is-kuratowski-finite-set

module _
  {l : Level} (X : 𝔽-Kuratowski l)
  where

  set-𝔽-Kuratowski : Set l
  set-𝔽-Kuratowski = pr1 X

  type-𝔽-Kuratowski : UU l
  type-𝔽-Kuratowski = type-Set set-𝔽-Kuratowski

  is-set-type-𝔽-Kuratowski : is-set type-𝔽-Kuratowski
  is-set-type-𝔽-Kuratowski = is-set-type-Set set-𝔽-Kuratowski

  is-kuratowski-finite-set-𝔽-Kuratowski :
    is-kuratowski-finite-set set-𝔽-Kuratowski
  is-kuratowski-finite-set-𝔽-Kuratowski = pr2 X
```

## Properties

### A Kuratowski finite set is finite if and only if it has decidable equality

```agda
is-finite-has-decidable-equality-type-𝔽-Kuratowski :
  {l : Level} (X : 𝔽-Kuratowski l) →
  has-decidable-equality (type-𝔽-Kuratowski X) →
  is-finite (type-𝔽-Kuratowski X)
is-finite-has-decidable-equality-type-𝔽-Kuratowski X H =
  apply-universal-property-trunc-Prop
    ( is-kuratowski-finite-set-𝔽-Kuratowski X)
    ( is-finite-Prop (type-𝔽-Kuratowski X))
    ( λ (n , f , s) → is-finite-codomain (is-finite-Fin n) s H)

has-decidable-equality-is-finite-type-𝔽-Kuratowski :
  {l : Level} (X : 𝔽-Kuratowski l) →
  is-finite (type-𝔽-Kuratowski X) →
  has-decidable-equality (type-𝔽-Kuratowski X)
has-decidable-equality-is-finite-type-𝔽-Kuratowski X =
  has-decidable-equality-is-finite
```

## See also

- [Finite types](univalent-combinatorics.finite-types.md)
- [Dedekind-finite sets](univalent-combinatorics.dedekind-finite-sets.md)

## External links

- [Finiteness in Sheaf Topoi](https://grossack.site/2024/08/19/finiteness-in-sheaf-topoi),
  blog post by Chris Grossack
- [`Fin.Kuratowski`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Fin.Kuratowski.html)
  at TypeTopology
- [finite set](https://ncatlab.org/nlab/show/finite+set) at $n$Lab
- [finite object](https://ncatlab.org/nlab/show/finite+object) at $n$Lab
- [Finite set](https://en.wikipedia.org/wiki/Finite_set) at Wikipedia
