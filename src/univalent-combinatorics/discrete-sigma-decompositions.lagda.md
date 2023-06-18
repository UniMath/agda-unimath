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
  {l1 : Level} (l2 : Level) (A : 𝔽 l1)
  where

  discrete-Σ-Decomposition-𝔽 :
    Σ-Decomposition-𝔽 l1 l2 A
  discrete-Σ-Decomposition-𝔽 =
    map-Σ-Decomposition-𝔽-subtype-is-finite
      ( A)
      ( ( discrete-Σ-Decomposition l2 (type-𝔽 A)) ,
        ( is-finite-type-𝔽 A ,
          λ x → is-finite-raise-unit))

module _
  {l1 l2 l3 : Level} (A : 𝔽 l1)
  (D : Σ-Decomposition-𝔽 l2 l3 A)
  where

  is-discrete-Prop-Σ-Decomposition-𝔽 :
    Prop (l2 ⊔ l3)
  is-discrete-Prop-Σ-Decomposition-𝔽 =
    Π-Prop
      ( indexing-type-Σ-Decomposition-𝔽 A D)
      ( λ x → is-contr-Prop (cotype-Σ-Decomposition-𝔽 A D x))

  is-discrete-Σ-Decomposition-𝔽 :
    UU (l2 ⊔ l3)
  is-discrete-Σ-Decomposition-𝔽 =
    type-Prop is-discrete-Prop-Σ-Decomposition-𝔽

is-discrete-discrete-Σ-Decomposition-𝔽 :
  {l1 l2 : Level} (A : 𝔽 l1) →
  is-discrete-Σ-Decomposition-𝔽
    ( A)
    ( discrete-Σ-Decomposition-𝔽 l2 A)
is-discrete-discrete-Σ-Decomposition-𝔽 _ =
  is-discrete-discrete-Σ-Decomposition

type-discrete-Σ-Decomposition-𝔽 :
  {l1 l2 l3 : Level} (A : 𝔽 l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-discrete-Σ-Decomposition-𝔽 {l1} {l2} {l3} A =
  type-subtype (is-discrete-Prop-Σ-Decomposition-𝔽 {l1} {l2} {l3} A)
```

## Propositions

```agda
module _
  {l1 l2 l3 l4 : Level} (A : 𝔽 l1)
  (D : Σ-Decomposition-𝔽 l2 l3 A)
  ( is-discrete : is-discrete-Σ-Decomposition-𝔽 A D)
  where

  equiv-discrete-is-discrete-Σ-Decomposition-𝔽 :
    equiv-Σ-Decomposition-𝔽
      ( A)
      ( D)
      ( discrete-Σ-Decomposition-𝔽
        ( l4)
        ( A))
  equiv-discrete-is-discrete-Σ-Decomposition-𝔽 =
    equiv-discrete-is-discrete-Σ-Decomposition
      ( Σ-Decomposition-Σ-Decomposition-𝔽 A D)
      ( is-discrete)

is-contr-type-discrete-Σ-Decomposition-𝔽 :
  {l1 l2 : Level} (A : 𝔽 l1) →
  is-contr (type-discrete-Σ-Decomposition-𝔽 {l1} {l1} {l2} A)
pr1 ( is-contr-type-discrete-Σ-Decomposition-𝔽 {l1} {l2} A) =
  ( discrete-Σ-Decomposition-𝔽 l2 A ,
    is-discrete-discrete-Σ-Decomposition-𝔽 A)
pr2 ( is-contr-type-discrete-Σ-Decomposition-𝔽 {l1} {l2} A) =
  ( λ x →
    eq-type-subtype
      ( is-discrete-Prop-Σ-Decomposition-𝔽 A)
      ( inv
        ( eq-equiv-Σ-Decomposition-𝔽
          ( A)
          ( pr1 x)
          ( discrete-Σ-Decomposition-𝔽 l2 A)
          ( equiv-discrete-is-discrete-Σ-Decomposition-𝔽 A (pr1 x) (pr2 x)))))
```
