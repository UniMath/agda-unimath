# Kuratowsky finite sets

```agda
module univalent-combinatorics.kuratowsky-finite-sets where
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

A {{#concept "Kuratowsky finite set" agda=𝔽-Kuratowsky}} is a
[set](foundation-core.sets.md) `X` for which there exists a
[surjection](foundation.surjective-maps.md) into `X` from a standard finite
type. In other words, the Kuratowsky finite set are the
[set-quotient](foundation.set-quotients.md) of a
[standard finite type](univalent-combinatorics.standard-finite-types.md).

## Definition

```agda
is-kuratowsky-finite-set-Prop : {l : Level} → Set l → Prop l
is-kuratowsky-finite-set-Prop X =
  exists-structure-Prop ℕ (λ n → Fin n ↠ type-Set X)

is-kuratowsky-finite-set : {l : Level} → Set l → UU l
is-kuratowsky-finite-set X = type-Prop (is-kuratowsky-finite-set-Prop X)

𝔽-Kuratowsky : (l : Level) → UU (lsuc l)
𝔽-Kuratowsky l = Σ (Set l) is-kuratowsky-finite-set

module _
  {l : Level} (X : 𝔽-Kuratowsky l)
  where

  set-𝔽-Kuratowsky : Set l
  set-𝔽-Kuratowsky = pr1 X

  type-𝔽-Kuratowsky : UU l
  type-𝔽-Kuratowsky = type-Set set-𝔽-Kuratowsky

  is-set-type-𝔽-Kuratowsky : is-set type-𝔽-Kuratowsky
  is-set-type-𝔽-Kuratowsky = is-set-type-Set set-𝔽-Kuratowsky

  is-kuratowsky-finite-set-𝔽-Kuratowsky :
    is-kuratowsky-finite-set set-𝔽-Kuratowsky
  is-kuratowsky-finite-set-𝔽-Kuratowsky = pr2 X
```

## Properties

### A Kuratowsky finite set is finite if and only if it has decidable equality

```agda
is-finite-has-decidable-equality-type-𝔽-Kuratowsky :
  {l : Level} (X : 𝔽-Kuratowsky l) →
  has-decidable-equality (type-𝔽-Kuratowsky X) →
  is-finite (type-𝔽-Kuratowsky X)
is-finite-has-decidable-equality-type-𝔽-Kuratowsky X H =
  apply-universal-property-trunc-Prop
    ( is-kuratowsky-finite-set-𝔽-Kuratowsky X)
    ( is-finite-Prop (type-𝔽-Kuratowsky X))
    ( λ (n , f , s) → is-finite-codomain (is-finite-Fin n) s H)

has-decidable-equality-is-finite-type-𝔽-Kuratowsky :
  {l : Level} (X : 𝔽-Kuratowsky l) →
  is-finite (type-𝔽-Kuratowsky X) →
  has-decidable-equality (type-𝔽-Kuratowsky X)
has-decidable-equality-is-finite-type-𝔽-Kuratowsky X =
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
