# Subfinite types

```agda
module univalent-combinatorics.subfinite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.embeddings
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universe-levels

open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.subcounting
```

</details>

## Idea

A type `X` is {{#concept "subfinite" Agda=is-subfinite Agda=Subfinite-Type}} if
there [exists](foundation.existential-quantification.md) an
[embedding](foundation-core.embeddings.md) into a
[standard finite type](univalent-combinatorics.standard-finite-types.md).

## Definitions

### The predicate of being subfinite

```agda
is-subfinite-Prop : {l : Level} → UU l → Prop l
is-subfinite-Prop X = trunc-Prop (subcount X)

is-subfinite : {l : Level} → UU l → UU l
is-subfinite X = type-Prop (is-subfinite-Prop X)

is-prop-is-subfinite : {l : Level} {X : UU l} → is-prop (is-subfinite X)
is-prop-is-subfinite {X = X} = is-prop-type-Prop (is-subfinite-Prop X)
```

### The subuniverse of subfinite types

```agda
Subfinite-Type : (l : Level) → UU (lsuc l)
Subfinite-Type l = Σ (UU l) (is-subfinite)

module _
  {l : Level} (X : Subfinite-Type l)
  where

  type-Subfinite-Type : UU l
  type-Subfinite-Type = pr1 X

  is-subfinite-type-Subfinite-Type : is-subfinite type-Subfinite-Type
  is-subfinite-type-Subfinite-Type = pr2 X
```

## Properties

### Subfinite types are discrete

```agda
module _
  {l : Level} (X : Subfinite-Type l)
  where

  has-decidable-equality-type-Subfinite-Type :
    has-decidable-equality (type-Subfinite-Type X)
  has-decidable-equality-type-Subfinite-Type =
    rec-trunc-Prop
      ( has-decidable-equality-Prop (type-Subfinite-Type X))
      ( λ (k , f) → has-decidable-equality-emb f (has-decidable-equality-Fin k))
      ( is-subfinite-type-Subfinite-Type X)

  discrete-type-Subfinite-Type : Discrete-Type l
  discrete-type-Subfinite-Type =
    ( type-Subfinite-Type X , has-decidable-equality-type-Subfinite-Type)
```

### Subfinite types are sets

```agda
module _
  {l : Level} (X : Subfinite-Type l)
  where

  is-set-type-Subfinite-Type : is-set (type-Subfinite-Type X)
  is-set-type-Subfinite-Type =
    is-set-has-decidable-equality (has-decidable-equality-type-Subfinite-Type X)

  set-Subfinite-Type : Set l
  set-Subfinite-Type = (type-Subfinite-Type X , is-set-type-Subfinite-Type)
```

## See also

- [Finite types](univalent-combinatorics.finite-types.md)
- [Dedekind finite sets](univalent-combinatorics.dedekind-finite-sets.md)
- In [`univalent-combinatorics.surjective-maps`] it is shown that if a
  Kuratowski finite set has decidable equality, then it is in fact finite.

## External links

- [Finiteness in Sheaf Topoi](https://grossack.site/2024/08/19/finiteness-in-sheaf-topoi),
  blog post by Chris Grossack
- [`Fin.Kuratowski`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Fin.Kuratowski.html)
  at TypeTopology
- [finite set](https://ncatlab.org/nlab/show/finite+set) at $n$Lab
- [finite object](https://ncatlab.org/nlab/show/finite+object) at $n$Lab
- [Finite set](https://en.wikipedia.org/wiki/Finite_set) at Wikipedia

```

```
