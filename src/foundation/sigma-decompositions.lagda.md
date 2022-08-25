---
title: Σ-decompositions of types
---

```agda
module foundation.sigma-decompositions where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.inhabited-types
open import foundation.universe-levels
```

## Idea

A Σ-decomposition of a type `A` consists of a type `X` and a family of inhabited types `Y x` indexed by `x : A` equipped with an equivalence `A ≃ Σ X Y`. The type `X` is called the indexing type of the Σ-decomposition, the elements of `Y x` are called the cotypes of the Σ-decomposition, and the equivalence `A ≃ Σ X Y` is the matching correspondence of the Σ-decomposition

Note that types may have many Σ-decomposition. The type of Σ-decompositions of the unit type, for instance, is equivalent to the type of all pointed connected types. Alternatively, we may think of the type of Σ-decompositions of the unit type as the type of higher groupoid structures on a point, i.e., the type of higher group structures. 

We may restrict to Σ-decompositions where the indexing type is in a given subuniverse, such as the subuniverse of sets or the subuniverse of finite sets.

The type of set-indexed Σ-decompositions of a type `A` is equivalent to the type of equivalence relations on `A`.

## Definitions
### Definition
### General Σ-decompositions

```agda
Σ-Decomposition :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
Σ-Decomposition l2 l3 A =
  Σ ( UU l2)
    ( λ X →
      Σ ( X → Inhabited-Type l3)
        ( λ Y → A ≃ Σ X (λ x → type-Inhabited-Type (Y x))))

module _
  {l1 l2 l3 : Level} {A : UU l1} (D : Σ-Decomposition l2 l3 A)
  where

  indexing-type-Σ-Decomposition : UU l2
  indexing-type-Σ-Decomposition = pr1 D

  inhabited-cotype-Σ-Decomposition :
    indexing-type-Σ-Decomposition → Inhabited-Type l3
  inhabited-cotype-Σ-Decomposition = pr1 (pr2 D)

  cotype-Σ-Decomposition : indexing-type-Σ-Decomposition → UU l3
  cotype-Σ-Decomposition x =
    type-Inhabited-Type (inhabited-cotype-Σ-Decomposition x)

  is-inhabited-cotype-Σ-Decomposition :
    (x : indexing-type-Σ-Decomposition) →
    is-inhabited (cotype-Σ-Decomposition x)
  is-inhabited-cotype-Σ-Decomposition x =
    is-inhabited-type-Inhabited-Type (inhabited-cotype-Σ-Decomposition x)

  matching-correspondence-Σ-Decomposition :
    A ≃ Σ indexing-type-Σ-Decomposition cotype-Σ-Decomposition
  matching-correspondence-Σ-Decomposition = pr2 (pr2 D)

  map-matching-correspondence-Σ-Decomposition :
    A → Σ indexing-type-Σ-Decomposition cotype-Σ-Decomposition
  map-matching-correspondence-Σ-Decomposition =
    map-equiv matching-correspondence-Σ-Decomposition
```
