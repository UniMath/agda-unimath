# Finite trivial Σ-Decompositions

```agda
module univalent-combinatorics.trivial-sigma-decompositions where

open import foundation.trivial-sigma-decompositions public

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.sigma-decompositions

```

## Definitions

```agda
module _
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
  (D : Σ-Decomposition-𝔽 l2 l3 A)
  where

  is-trivial-Prop-Σ-Decomposition-𝔽 :
    Prop l2
  is-trivial-Prop-Σ-Decomposition-𝔽 =
    is-contr-Prop (indexing-type-Σ-Decomposition-𝔽 D)

  is-trivial-Σ-Decomposition-𝔽 :
    UU (l2)
  is-trivial-Σ-Decomposition-𝔽 =
    type-Prop (is-trivial-Prop-Σ-Decomposition-𝔽)

is-trivial-trivial-inhabited-Σ-Decomposition-𝔽 :
  {l1 l2 : Level} {A : UU l1} (is-finite-A : is-finite A) (p : is-inhabited A) →
  is-trivial-Σ-Decomposition-𝔽
    ( trivial-inhabited-Σ-Decomposition-𝔽 l2 A is-finite-A p)
is-trivial-trivial-inhabited-Σ-Decomposition-𝔽 is-finite-A p =
  is-trivial-trivial-inhabited-Σ-Decomposition p

type-trivial-Σ-Decomposition-𝔽 :
  {l1 l2 l3 : Level} {A : UU l1} → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-trivial-Σ-Decomposition-𝔽 {l1} {l2} {l3} {A}=
  type-subtype (is-trivial-Prop-Σ-Decomposition-𝔽 {l1} {l2} {l3} {A})
```

## Propositions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1}
  (D : Σ-Decomposition-𝔽 l2 l3 A)
  (is-trivial : is-trivial-Σ-Decomposition-𝔽 D)
  where

  equiv-trivial-is-trivial-Σ-Decomposition-𝔽 :
    equiv-Σ-Decomposition-𝔽
      ( D)
      ( trivial-inhabited-Σ-Decomposition-𝔽
        ( l4)
        ( A)
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
```
