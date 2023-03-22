# Finite discrete Σ-Decompositions

```agda
module univalent-combinatorics.discrete-sigma-decompositions where
<<<<<<< HEAD

=======
```

<details><summary>Imports</summary>

```agda
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
open import foundation.discrete-sigma-decompositions public

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.sigma-decompositions
```

<<<<<<< HEAD
=======
</details>

>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
## Definitions

```agda
module _
<<<<<<< HEAD
  {l1 : Level} (l2 : Level) (A : UU l1) (is-finite-A : is-finite A)
=======
  {l1 : Level} (l2 : Level) (A : 𝔽 l1)
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
  where

  discrete-Σ-Decomposition-𝔽 :
    Σ-Decomposition-𝔽 l1 l2 A
  discrete-Σ-Decomposition-𝔽 =
    map-Σ-Decomposition-𝔽-subtype-is-finite
<<<<<<< HEAD
      ( ( discrete-Σ-Decomposition l2 A) ,
        ( is-finite-A ,
          λ x → is-finite-raise-unit))

module _
  {l1 l2 l3 : Level} {A : UU l1}
=======
      ( A)
      ( ( discrete-Σ-Decomposition l2 (type-𝔽 A)) ,
        ( is-finite-type-𝔽 A ,
          λ x → is-finite-raise-unit))

module _
  {l1 l2 l3 : Level} (A : 𝔽 l1)
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
  (D : Σ-Decomposition-𝔽 l2 l3 A)
  where

  is-discrete-Prop-Σ-Decomposition-𝔽 :
    Prop (l2 ⊔ l3)
  is-discrete-Prop-Σ-Decomposition-𝔽 =
    Π-Prop
<<<<<<< HEAD
      ( indexing-type-Σ-Decomposition-𝔽 D)
      ( λ x → is-contr-Prop (cotype-Σ-Decomposition-𝔽 D x))
=======
      ( indexing-type-Σ-Decomposition-𝔽 A D)
      ( λ x → is-contr-Prop (cotype-Σ-Decomposition-𝔽 A D x))
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3

  is-discrete-Σ-Decomposition-𝔽 :
    UU (l2 ⊔ l3)
  is-discrete-Σ-Decomposition-𝔽 =
    type-Prop is-discrete-Prop-Σ-Decomposition-𝔽

is-discrete-discrete-Σ-Decomposition-𝔽 :
<<<<<<< HEAD
  {l1 l2 : Level} {A : UU l1} → (is-finite-A : is-finite A) →
  is-discrete-Σ-Decomposition-𝔽
    ( discrete-Σ-Decomposition-𝔽 l2 A is-finite-A)
=======
  {l1 l2 : Level} (A : 𝔽 l1) →
  is-discrete-Σ-Decomposition-𝔽
    ( A)
    ( discrete-Σ-Decomposition-𝔽 l2 A)
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
is-discrete-discrete-Σ-Decomposition-𝔽 _ =
  is-discrete-discrete-Σ-Decomposition

type-discrete-Σ-Decomposition-𝔽 :
<<<<<<< HEAD
  {l1 l2 l3 : Level} {A : UU l1} → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-discrete-Σ-Decomposition-𝔽 {l1} {l2} {l3} {A} =
  type-subtype (is-discrete-Prop-Σ-Decomposition-𝔽 {l1} {l2} {l3} {A})
=======
  {l1 l2 l3 : Level} (A : 𝔽 l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-discrete-Σ-Decomposition-𝔽 {l1} {l2} {l3} A =
  type-subtype (is-discrete-Prop-Σ-Decomposition-𝔽 {l1} {l2} {l3} A)
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```

## Propositions

```agda
module _
<<<<<<< HEAD
  {l1 l2 l3 l4 : Level} {A : UU l1}
  (D : Σ-Decomposition-𝔽 l2 l3 A)
  ( is-discrete : is-discrete-Σ-Decomposition-𝔽 D)
=======
  {l1 l2 l3 l4 : Level} (A : 𝔽 l1)
  (D : Σ-Decomposition-𝔽 l2 l3 A)
  ( is-discrete : is-discrete-Σ-Decomposition-𝔽 A D)
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
  where

  equiv-discrete-is-discrete-Σ-Decomposition-𝔽 :
    equiv-Σ-Decomposition-𝔽
<<<<<<< HEAD
      ( D)
      ( discrete-Σ-Decomposition-𝔽
        ( l4)
        ( A)
        ( is-finite-base-type-Σ-Decomposition-𝔽 D))
  equiv-discrete-is-discrete-Σ-Decomposition-𝔽 =
    equiv-discrete-is-discrete-Σ-Decomposition
      ( Σ-Decomposition-Σ-Decomposition-𝔽 D)
      ( is-discrete)

is-contr-type-discrete-Σ-Decomposition-𝔽 :
  {l1 l2 : Level} {A : UU l1} → (is-finite-A : is-finite A) →
  is-contr (type-discrete-Σ-Decomposition-𝔽 {l1} {l1} {l2} {A})
pr1 ( is-contr-type-discrete-Σ-Decomposition-𝔽 {l1} {l2} {A} is-finite-A) =
  ( discrete-Σ-Decomposition-𝔽 l2 A is-finite-A ,
    is-discrete-discrete-Σ-Decomposition-𝔽 is-finite-A)
pr2 ( is-contr-type-discrete-Σ-Decomposition-𝔽 {l1} {l2} {A} is-finite-A) =
  ( λ x →
    eq-type-subtype
      ( is-discrete-Prop-Σ-Decomposition-𝔽)
      ( inv
        ( eq-equiv-Σ-Decomposition-𝔽
          ( pr1 x)
          ( discrete-Σ-Decomposition-𝔽 l2 A is-finite-A)
          ( equiv-discrete-is-discrete-Σ-Decomposition-𝔽 (pr1 x) (pr2 x)))))
=======
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
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```
