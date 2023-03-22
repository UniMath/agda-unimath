# Finite trivial Σ-Decompositions

```agda
module univalent-combinatorics.trivial-sigma-decompositions where
<<<<<<< HEAD

=======
```

<details><summary>Imports</summary>

```agda
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
open import foundation.trivial-sigma-decompositions public

open import foundation.contractible-types
open import foundation.dependent-pair-types
<<<<<<< HEAD
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-propositional-truncation
=======
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.subtypes
<<<<<<< HEAD
open import foundation.type-arithmetic-dependent-pair-types
=======
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
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
  where

  trivial-inhabited-Σ-Decomposition-𝔽 :
    (p : is-inhabited A) → Σ-Decomposition-𝔽 l2 l1 A
  trivial-inhabited-Σ-Decomposition-𝔽 p =
    map-Σ-Decomposition-𝔽-subtype-is-finite
      ( ( trivial-inhabited-Σ-Decomposition l2 A p) ,
        ( is-finite-raise-unit , λ x → is-finite-A))

  trivial-empty-Σ-Decomposition-𝔽 :
    (p : is-empty A) → Σ-Decomposition-𝔽 lzero lzero A
  trivial-empty-Σ-Decomposition-𝔽 p =
    map-Σ-Decomposition-𝔽-subtype-is-finite
      ( ( trivial-empty-Σ-Decomposition l2 A p) ,
        ( is-finite-is-empty id ,
          λ x → ex-falso x))

module _
  {l1 l2 l3 : Level} {A : UU l1}
=======
  {l1 : Level} (l2 : Level) (A : 𝔽 l1)
  where

  trivial-inhabited-Σ-Decomposition-𝔽 :
    (p : is-inhabited (type-𝔽 A)) → Σ-Decomposition-𝔽 l2 l1 A
  trivial-inhabited-Σ-Decomposition-𝔽 p =
    map-Σ-Decomposition-𝔽-subtype-is-finite
      ( A)
      ( ( trivial-inhabited-Σ-Decomposition l2 (type-𝔽 A) p) ,
        ( is-finite-raise-unit , λ x → is-finite-type-𝔽 A))

module _
  {l1 l2 l3 : Level} (A : 𝔽 l1)
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
  (D : Σ-Decomposition-𝔽 l2 l3 A)
  where

  is-trivial-Prop-Σ-Decomposition-𝔽 :
    Prop l2
  is-trivial-Prop-Σ-Decomposition-𝔽 =
<<<<<<< HEAD
    is-contr-Prop (indexing-type-Σ-Decomposition-𝔽 D)
=======
    is-contr-Prop (indexing-type-Σ-Decomposition-𝔽 A D)
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3

  is-trivial-Σ-Decomposition-𝔽 :
    UU (l2)
  is-trivial-Σ-Decomposition-𝔽 =
    type-Prop (is-trivial-Prop-Σ-Decomposition-𝔽)

is-trivial-trivial-inhabited-Σ-Decomposition-𝔽 :
<<<<<<< HEAD
  {l1 l2 : Level} {A : UU l1} (is-finite-A : is-finite A) (p : is-inhabited A) →
  is-trivial-Σ-Decomposition-𝔽
    ( trivial-inhabited-Σ-Decomposition-𝔽 l2 A is-finite-A p)
is-trivial-trivial-inhabited-Σ-Decomposition-𝔽 is-finite-A p =
  is-trivial-trivial-inhabited-Σ-Decomposition p

type-trivial-Σ-Decomposition-𝔽 :
  {l1 l2 l3 : Level} {A : UU l1} → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-trivial-Σ-Decomposition-𝔽 {l1} {l2} {l3} {A}=
  type-subtype (is-trivial-Prop-Σ-Decomposition-𝔽 {l1} {l2} {l3} {A})
=======
  {l1 l2 : Level} (A : 𝔽 l1) (p : is-inhabited (type-𝔽 A)) →
  is-trivial-Σ-Decomposition-𝔽
    ( A)
    ( trivial-inhabited-Σ-Decomposition-𝔽 l2 A p)
is-trivial-trivial-inhabited-Σ-Decomposition-𝔽 A p =
  is-trivial-trivial-inhabited-Σ-Decomposition p

type-trivial-Σ-Decomposition-𝔽 :
  {l1 l2 l3 : Level} (A : 𝔽 l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-trivial-Σ-Decomposition-𝔽 {l1} {l2} {l3} A =
  type-subtype (is-trivial-Prop-Σ-Decomposition-𝔽 {l1} {l2} {l3} A)
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```

## Propositions

```agda
module _
<<<<<<< HEAD
  {l1 l2 l3 l4 : Level} {A : UU l1}
  (D : Σ-Decomposition-𝔽 l2 l3 A)
  (is-trivial : is-trivial-Σ-Decomposition-𝔽 D)
=======
  {l1 l2 l3 l4 : Level} (A : 𝔽 l1)
  (D : Σ-Decomposition-𝔽 l2 l3 A)
  (is-trivial : is-trivial-Σ-Decomposition-𝔽 A D)
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
  where

  equiv-trivial-is-trivial-Σ-Decomposition-𝔽 :
    equiv-Σ-Decomposition-𝔽
<<<<<<< HEAD
=======
      ( A)
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
      ( D)
      ( trivial-inhabited-Σ-Decomposition-𝔽
        ( l4)
        ( A)
<<<<<<< HEAD
        ( is-finite-base-type-Σ-Decomposition-𝔽 D)
        ( is-inhabited-base-type-is-trivial-Σ-Decomposition {l1} {l2} {l3} {l4}
          ( Σ-Decomposition-Σ-Decomposition-𝔽 D)
          ( is-trivial)))
  equiv-trivial-is-trivial-Σ-Decomposition-𝔽 =
    equiv-trivial-is-trivial-Σ-Decomposition
      ( Σ-Decomposition-Σ-Decomposition-𝔽 D)
      ( is-trivial)

is-contr-type-trivial-Σ-Decomposition-𝔽 :
  {l1 l2 : Level} {A : UU l1} →
  (is-finite-A : is-finite A) (p : is-inhabited A) →
  is-contr (type-trivial-Σ-Decomposition-𝔽 {l1} {l2} {l1} {A})
pr1 ( is-contr-type-trivial-Σ-Decomposition-𝔽 {l1} {l2} {A} is-finite-A p) =
  ( trivial-inhabited-Σ-Decomposition-𝔽 l2 A is-finite-A p ,
    is-trivial-trivial-inhabited-Σ-Decomposition-𝔽 is-finite-A p)
pr2 ( is-contr-type-trivial-Σ-Decomposition-𝔽 {l1} {l2} {A} is-finite-A p) =
   ( λ x →
     eq-type-subtype
       ( is-trivial-Prop-Σ-Decomposition-𝔽)
       ( inv
         ( eq-equiv-Σ-Decomposition-𝔽
           ( pr1 x)
           ( trivial-inhabited-Σ-Decomposition-𝔽 l2 A is-finite-A p)
           ( equiv-trivial-is-trivial-Σ-Decomposition-𝔽 (pr1 x) (pr2 x)))))
=======
        ( is-inhabited-base-type-is-trivial-Σ-Decomposition {l1} {l2} {l3} {l4}
          ( Σ-Decomposition-Σ-Decomposition-𝔽 A D)
          ( is-trivial)))
  equiv-trivial-is-trivial-Σ-Decomposition-𝔽 =
    equiv-trivial-is-trivial-Σ-Decomposition
      ( Σ-Decomposition-Σ-Decomposition-𝔽 A D)
      ( is-trivial)

is-contr-type-trivial-Σ-Decomposition-𝔽 :
  {l1 l2 : Level} (A : 𝔽 l1) → (p : is-inhabited (type-𝔽 A)) →
  is-contr (type-trivial-Σ-Decomposition-𝔽 {l1} {l2} {l1} A)
pr1 ( is-contr-type-trivial-Σ-Decomposition-𝔽 {l1} {l2} A p) =
  ( trivial-inhabited-Σ-Decomposition-𝔽 l2 A p ,
    is-trivial-trivial-inhabited-Σ-Decomposition-𝔽 A p)
pr2 ( is-contr-type-trivial-Σ-Decomposition-𝔽 {l1} {l2} A p) =
   ( λ x →
     eq-type-subtype
       ( is-trivial-Prop-Σ-Decomposition-𝔽 A)
       ( inv
         ( eq-equiv-Σ-Decomposition-𝔽
           ( A)
           ( pr1 x)
           ( trivial-inhabited-Σ-Decomposition-𝔽 l2 A p)
           ( equiv-trivial-is-trivial-Σ-Decomposition-𝔽 A (pr1 x) (pr2 x)))))
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```
