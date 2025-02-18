# Finite discrete Σ-decompositions

```agda
module univalent-combinatorics.discrete-sigma-decompositions where

open import foundation.discrete-sigma-decompositions public
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
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

  discrete-Σ-Decomposition-Finite-Type :
    Σ-Decomposition-Finite-Type l1 l2 A
  discrete-Σ-Decomposition-Finite-Type =
    map-Σ-Decomposition-Finite-Type-subtype-is-finite
      ( A)
      ( ( discrete-Σ-Decomposition l2 (type-Finite-Type A)) ,
        ( is-finite-type-Finite-Type A ,
          λ x → is-finite-raise-unit))

module _
  {l1 l2 l3 : Level} (A : Finite-Type l1)
  (D : Σ-Decomposition-Finite-Type l2 l3 A)
  where

  is-discrete-Prop-Σ-Decomposition-Finite-Type :
    Prop (l2 ⊔ l3)
  is-discrete-Prop-Σ-Decomposition-Finite-Type =
    Π-Prop
      ( indexing-type-Σ-Decomposition-Finite-Type A D)
      ( λ x → is-contr-Prop (cotype-Σ-Decomposition-Finite-Type A D x))

  is-discrete-Σ-Decomposition-Finite-Type :
    UU (l2 ⊔ l3)
  is-discrete-Σ-Decomposition-Finite-Type =
    type-Prop is-discrete-Prop-Σ-Decomposition-Finite-Type

is-discrete-discrete-Σ-Decomposition-Finite-Type :
  {l1 l2 : Level} (A : Finite-Type l1) →
  is-discrete-Σ-Decomposition-Finite-Type
    ( A)
    ( discrete-Σ-Decomposition-Finite-Type l2 A)
is-discrete-discrete-Σ-Decomposition-Finite-Type _ =
  is-discrete-discrete-Σ-Decomposition

type-discrete-Σ-Decomposition-Finite-Type :
  {l1 l2 l3 : Level} (A : Finite-Type l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-discrete-Σ-Decomposition-Finite-Type {l1} {l2} {l3} A =
  type-subtype (is-discrete-Prop-Σ-Decomposition-Finite-Type {l1} {l2} {l3} A)
```

## Propositions

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Finite-Type l1)
  (D : Σ-Decomposition-Finite-Type l2 l3 A)
  ( is-discrete : is-discrete-Σ-Decomposition-Finite-Type A D)
  where

  equiv-discrete-is-discrete-Σ-Decomposition-Finite-Type :
    equiv-Σ-Decomposition-Finite-Type
      ( A)
      ( D)
      ( discrete-Σ-Decomposition-Finite-Type
        ( l4)
        ( A))
  equiv-discrete-is-discrete-Σ-Decomposition-Finite-Type =
    equiv-discrete-is-discrete-Σ-Decomposition
      ( Σ-Decomposition-Σ-Decomposition-Finite-Type A D)
      ( is-discrete)

is-contr-type-discrete-Σ-Decomposition-Finite-Type :
  {l1 l2 : Level} (A : Finite-Type l1) →
  is-contr (type-discrete-Σ-Decomposition-Finite-Type {l1} {l1} {l2} A)
pr1 ( is-contr-type-discrete-Σ-Decomposition-Finite-Type {l1} {l2} A) =
  ( discrete-Σ-Decomposition-Finite-Type l2 A ,
    is-discrete-discrete-Σ-Decomposition-Finite-Type A)
pr2 ( is-contr-type-discrete-Σ-Decomposition-Finite-Type {l1} {l2} A) =
  ( λ x →
    eq-type-subtype
      ( is-discrete-Prop-Σ-Decomposition-Finite-Type A)
      ( inv
        ( eq-equiv-Σ-Decomposition-Finite-Type
          ( A)
          ( pr1 x)
          ( discrete-Σ-Decomposition-Finite-Type l2 A)
          ( equiv-discrete-is-discrete-Σ-Decomposition-Finite-Type A
            ( pr1 x)
            ( pr2 x)))))
```
