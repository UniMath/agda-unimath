# Trivial relaxed Σ-decompositions

```agda
module foundation.trivial-relaxed-sigma-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.relaxed-sigma-decompositions
open import foundation.transposition-identifications-along-equivalences
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Idea

A relaxed Σ-decomposition is said to be **trivial** if its indexing type is
contractible.

## Definitions

### The predicate of being a trivial relaxed Σ-decomposition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (D : Relaxed-Σ-Decomposition l2 l3 A)
  where

  is-trivial-relaxed-Σ-decomposition-Prop : Prop l2
  is-trivial-relaxed-Σ-decomposition-Prop =
    is-contr-Prop (indexing-type-Relaxed-Σ-Decomposition D)

  is-trivial-Relaxed-Σ-Decomposition : UU l2
  is-trivial-Relaxed-Σ-Decomposition =
    type-Prop is-trivial-relaxed-Σ-decomposition-Prop
```

### The trivial relaxed Σ-decomposition

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  trivial-Relaxed-Σ-Decomposition : Relaxed-Σ-Decomposition l2 l1 A
  pr1 (trivial-Relaxed-Σ-Decomposition) = raise-unit l2
  pr1 (pr2 (trivial-Relaxed-Σ-Decomposition)) x = A
  pr2 (pr2 (trivial-Relaxed-Σ-Decomposition)) =
    inv-left-unit-law-Σ-is-contr
      ( is-contr-raise-unit)
      ( raise-star)

is-trivial-trivial-Relaxed-Σ-Decomposition :
  {l1 l2 : Level} {A : UU l1} →
  is-trivial-Relaxed-Σ-Decomposition (trivial-Relaxed-Σ-Decomposition l2 A)
is-trivial-trivial-Relaxed-Σ-Decomposition = is-contr-raise-unit
```

## Propositions

### Any trivial relaxed Σ-decomposition is equivalent to the standard trivial relaxed Σ-decomposition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1}
  (D : Relaxed-Σ-Decomposition l2 l3 A)
  ( is-trivial : is-trivial-Relaxed-Σ-Decomposition D)
  where

  equiv-trivial-is-trivial-Relaxed-Σ-Decomposition :
    equiv-Relaxed-Σ-Decomposition D (trivial-Relaxed-Σ-Decomposition l4 A)
  pr1 equiv-trivial-is-trivial-Relaxed-Σ-Decomposition =
    equiv-raise-unit-is-contr is-trivial
  pr1 (pr2 equiv-trivial-is-trivial-Relaxed-Σ-Decomposition) x =
    ( inv-equiv (matching-correspondence-Relaxed-Σ-Decomposition D)) ∘e
    ( inv-left-unit-law-Σ-is-contr is-trivial x)
  pr2 (pr2 equiv-trivial-is-trivial-Relaxed-Σ-Decomposition) a =
    eq-pair-eq-fiber
      ( map-inv-eq-transpose-equiv
        ( inv-equiv (matching-correspondence-Relaxed-Σ-Decomposition D))
        ( refl))
```

### The type of all trivial relaxed Σ-decompositions is contractible

```agda
is-contr-type-trivial-Relaxed-Σ-Decomposition :
  {l1 l2 : Level} {A : UU l1} →
  is-contr
    ( type-subtype (is-trivial-relaxed-Σ-decomposition-Prop {l1} {l2} {l1} {A}))
pr1 ( is-contr-type-trivial-Relaxed-Σ-Decomposition {l1} {l2} {A}) =
  ( trivial-Relaxed-Σ-Decomposition l2 A ,
    is-trivial-trivial-Relaxed-Σ-Decomposition {l1} {l2} {A})
pr2 ( is-contr-type-trivial-Relaxed-Σ-Decomposition {l1} {l2} {A}) D =
    eq-type-subtype
      ( is-trivial-relaxed-Σ-decomposition-Prop)
      ( inv
        ( eq-equiv-Relaxed-Σ-Decomposition
          ( pr1 D)
          ( trivial-Relaxed-Σ-Decomposition l2 A)
          ( equiv-trivial-is-trivial-Relaxed-Σ-Decomposition (pr1 D) (pr2 D))))
```
