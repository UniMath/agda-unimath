# Unlabelled structures of finite species

```agda
module species.unlabelled-structures-species where
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

The type of unlabelled `F`-structures of order `n` of a species `F` is the type
of sets `X` of size `n` equipped with an `F`-structure. Two unlabelled
`F`-structures of order `n` are considered to be the same if the underlying sets
are isomorphic and the `F`-structure of the first transports along this
isomorphism to the `F`-structure of the second. It will automatically follow
from the univalence axiom that the identity type of the type of unlabelled
`F`-structures of order `n` captures this idea.

## Definitions

### Unlabelled structures of a species

```agda
unlabelled-structure-species-types :
  {l1 l2 : Level} (F : species-types l1 l2) → ℕ → UU (lsuc l1 ⊔ l2)
unlabelled-structure-species-types {l1} {l2} F n =
  Σ (UU-Fin l1 n) (λ X → F (type-UU-Fin n X))

module _
  {l1 l2 : Level} (F : species-types l1 l2) {k : ℕ}
  (X : unlabelled-structure-species-types F k)
  where

  type-of-cardinality-unlabelled-structure-species-types : UU-Fin l1 k
  type-of-cardinality-unlabelled-structure-species-types = pr1 X

  type-unlabelled-structure-species-types : UU l1
  type-unlabelled-structure-species-types =
    type-UU-Fin k type-of-cardinality-unlabelled-structure-species-types

  has-cardinality-type-unlabelled-structure-species-types :
    has-cardinality k type-unlabelled-structure-species-types
  has-cardinality-type-unlabelled-structure-species-types =
    has-cardinality-type-UU-Fin
      k
      type-of-cardinality-unlabelled-structure-species-types

  finite-type-unlabelled-structure-species-types : 𝔽 l1
  finite-type-unlabelled-structure-species-types =
    finite-type-UU-Fin k type-of-cardinality-unlabelled-structure-species-types

  structure-unlabelled-structure-species-types :
    F type-unlabelled-structure-species-types
  structure-unlabelled-structure-species-types = pr2 X
```

### Equivalences of unlabelled structures of a species

This remains to be defined.
