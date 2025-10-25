# Unlabeled structures of finite species

```agda
module species.unlabeled-structures-species where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import species.species-of-types

open import univalent-combinatorics.finite-types
```

</details>

## Idea

The type of
{{#concept "unlabeled `F`-structures" Disambiguation="of a species of types" Agda=unlabeled-structure-species-types}}
of order `n` of a [species](species.species-of-types.md) `F` is the type of
[sets](foundation-core.sets.md) `X` of size `n` equipped with an `F`-structure.
Two unlabeled `F`-structures of order `n` are considered to be the same if the
underlying sets are isomorphic and the `F`-structure of the first transports
along this isomorphism to the `F`-structure of the second. It will automatically
follow from the [univalence axiom](foundation.univalence.md) that the
[identity type](foundation-core.identity-types.md) of the type of unlabeled
`F`-structures of order `n` captures this idea.

## Definitions

### Unlabeled structures of a species

```agda
unlabeled-structure-species-types :
  {l1 l2 : Level} (F : species-types l1 l2) → ℕ → UU (lsuc l1 ⊔ l2)
unlabeled-structure-species-types {l1} {l2} F n =
  Σ ( Type-With-Cardinality-ℕ l1 n)
    ( λ X → F (type-Type-With-Cardinality-ℕ n X))

module _
  {l1 l2 : Level} (F : species-types l1 l2) {k : ℕ}
  (X : unlabeled-structure-species-types F k)
  where

  type-of-cardinality-unlabeled-structure-species-types :
    Type-With-Cardinality-ℕ l1 k
  type-of-cardinality-unlabeled-structure-species-types = pr1 X

  type-unlabeled-structure-species-types : UU l1
  type-unlabeled-structure-species-types =
    type-Type-With-Cardinality-ℕ k
      type-of-cardinality-unlabeled-structure-species-types

  has-cardinality-type-unlabeled-structure-species-types :
    has-cardinality-ℕ k type-unlabeled-structure-species-types
  has-cardinality-type-unlabeled-structure-species-types =
    has-cardinality-type-Type-With-Cardinality-ℕ
      k
      type-of-cardinality-unlabeled-structure-species-types

  finite-type-unlabeled-structure-species-types : Finite-Type l1
  finite-type-unlabeled-structure-species-types =
    finite-type-Type-With-Cardinality-ℕ k
      type-of-cardinality-unlabeled-structure-species-types

  structure-unlabeled-structure-species-types :
    F type-unlabeled-structure-species-types
  structure-unlabeled-structure-species-types = pr2 X
```

### Equivalences of unlabeled structures of a species

This remains to be defined.
[#741](https://github.com/UniMath/agda-unimath/issues/741)
