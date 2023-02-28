# Finite discrete Σ-Decompositions

```agda
module univalent-combinatorics.discrete-sigma-decompositions where

open import foundation.discrete-sigma-decompositions public

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.sigma-decompositions
```

## Definitions

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1) (is-finite-A : is-finite A)
  where

  discrete-Σ-Decomposition-𝔽 :
    Σ-Decomposition-𝔽 l1 l2 A
  discrete-Σ-Decomposition-𝔽 =
    map-Σ-Decomposition-𝔽-subtype-is-finite
      ( ( discrete-Σ-Decomposition l2 A) ,
        ( is-finite-A ,
          λ x → is-finite-raise-unit))


module _
  {l1 l2 l3 : Level} {A : UU l1}
  (D : Σ-Decomposition-𝔽 l2 l3 A)
  where

  is-discrete-Prop-Σ-Decomposition-𝔽 :
    Prop (l2 ⊔ l3)
  is-discrete-Prop-Σ-Decomposition-𝔽 =
    Π-Prop
      ( indexing-type-Σ-Decomposition-𝔽 D)
      ( λ x → is-contr-Prop (cotype-Σ-Decomposition-𝔽 D x))

  is-discrete-Σ-Decomposition-𝔽 :
    UU (l2 ⊔ l3)
  is-discrete-Σ-Decomposition-𝔽 =
    type-Prop is-discrete-Prop-Σ-Decomposition-𝔽
```

## Propositions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1}
  (D : Σ-Decomposition-𝔽 l2 l3 A)
  ( is-discrete : is-discrete-Σ-Decomposition-𝔽 D)
  where

  equiv-discrete-is-discrete-Σ-Decomposition-𝔽 :
    equiv-Σ-Decomposition-𝔽
      ( D)
      ( discrete-Σ-Decomposition-𝔽 l4 A ( is-finite-base-type-Σ-Decomposition-𝔽 D))
  equiv-discrete-is-discrete-Σ-Decomposition-𝔽 =
    equiv-discrete-is-discrete-Σ-Decomposition
      ( Σ-Decomposition-Σ-Decomposition-𝔽 D)
      ( is-discrete)

```

