# Finite trivial Σ-decompositions

```agda
module univalent-combinatorics.trivial-sigma-decompositions where

open import foundation.trivial-sigma-decompositions public
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.sigma-decompositions
```

</details>

## Definitions

```agda
module _
  {l1 : Level} (l2 : Level) (A : Finite-Type l1)
  where

  trivial-inhabited-Σ-Decomposition-Finite-Type :
    is-inhabited (type-Finite-Type A) → Σ-Decomposition-Finite-Type l2 l1 A
  trivial-inhabited-Σ-Decomposition-Finite-Type p =
    map-Σ-Decomposition-Finite-Type-subtype-is-finite
      ( A)
      ( ( trivial-inhabited-Σ-Decomposition l2 (type-Finite-Type A) p) ,
        ( is-finite-raise-unit , λ x → is-finite-type-Finite-Type A))

module _
  {l1 l2 l3 : Level} (A : Finite-Type l1)
  (D : Σ-Decomposition-Finite-Type l2 l3 A)
  where

  is-trivial-Prop-Σ-Decomposition-Finite-Type :
    Prop l2
  is-trivial-Prop-Σ-Decomposition-Finite-Type =
    is-contr-Prop (indexing-type-Σ-Decomposition-Finite-Type A D)

  is-trivial-Σ-Decomposition-Finite-Type :
    UU (l2)
  is-trivial-Σ-Decomposition-Finite-Type =
    type-Prop (is-trivial-Prop-Σ-Decomposition-Finite-Type)

is-trivial-trivial-inhabited-Σ-Decomposition-Finite-Type :
  {l1 l2 : Level} (A : Finite-Type l1) (p : is-inhabited (type-Finite-Type A)) →
  is-trivial-Σ-Decomposition-Finite-Type
    ( A)
    ( trivial-inhabited-Σ-Decomposition-Finite-Type l2 A p)
is-trivial-trivial-inhabited-Σ-Decomposition-Finite-Type A p =
  is-trivial-trivial-inhabited-Σ-Decomposition p

type-trivial-Σ-Decomposition-Finite-Type :
  {l1 l2 l3 : Level} (A : Finite-Type l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-trivial-Σ-Decomposition-Finite-Type {l1} {l2} {l3} A =
  type-subtype (is-trivial-Prop-Σ-Decomposition-Finite-Type {l1} {l2} {l3} A)
```

## Propositions

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Finite-Type l1)
  (D : Σ-Decomposition-Finite-Type l2 l3 A)
  (is-trivial : is-trivial-Σ-Decomposition-Finite-Type A D)
  where

  equiv-trivial-is-trivial-Σ-Decomposition-Finite-Type :
    equiv-Σ-Decomposition-Finite-Type
      ( A)
      ( D)
      ( trivial-inhabited-Σ-Decomposition-Finite-Type
        ( l4)
        ( A)
        ( is-inhabited-base-type-is-trivial-Σ-Decomposition {l1} {l2} {l3} {l4}
          ( Σ-Decomposition-Σ-Decomposition-Finite-Type A D)
          ( is-trivial)))
  equiv-trivial-is-trivial-Σ-Decomposition-Finite-Type =
    equiv-trivial-is-trivial-Σ-Decomposition
      ( Σ-Decomposition-Σ-Decomposition-Finite-Type A D)
      ( is-trivial)

is-contr-type-trivial-Σ-Decomposition-Finite-Type :
  {l1 l2 : Level} (A : Finite-Type l1) (p : is-inhabited (type-Finite-Type A)) →
  is-contr (type-trivial-Σ-Decomposition-Finite-Type {l1} {l2} {l1} A)
pr1 ( is-contr-type-trivial-Σ-Decomposition-Finite-Type {l1} {l2} A p) =
  ( trivial-inhabited-Σ-Decomposition-Finite-Type l2 A p ,
    is-trivial-trivial-inhabited-Σ-Decomposition-Finite-Type A p)
pr2 ( is-contr-type-trivial-Σ-Decomposition-Finite-Type {l1} {l2} A p) x =
  eq-type-subtype
    ( is-trivial-Prop-Σ-Decomposition-Finite-Type A)
    ( inv
      ( eq-equiv-Σ-Decomposition-Finite-Type
        ( A)
        ( pr1 x)
        ( trivial-inhabited-Σ-Decomposition-Finite-Type l2 A p)
        ( equiv-trivial-is-trivial-Σ-Decomposition-Finite-Type A
          ( pr1 x)
          ( pr2 x))))
```
