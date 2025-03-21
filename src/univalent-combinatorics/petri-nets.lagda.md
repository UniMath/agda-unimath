# Petri-nets

```agda
module univalent-combinatorics.petri-nets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
```

</details>

## Idea

We give a definition of Petri nets due to Joachim Kock [[1]][1]

## Definition

```agda
Petri-Net : (l1 l2 l3 l4 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4)
Petri-Net l1 l2 l3 l4 =
  Σ ( Finite-Type l1)
    ( λ S →
      Σ ( Finite-Type l2)
        ( λ T →
          ( type-Finite-Type S → type-Finite-Type T → Finite-Type l3) ×
          ( type-Finite-Type T → type-Finite-Type S → Finite-Type l4)))

module _
  {l1 l2 l3 l4 : Level} (P : Petri-Net l1 l2 l3 l4)
  where

  place-finite-type-Petri-Net : Finite-Type l1
  place-finite-type-Petri-Net = pr1 P

  place-Petri-Net : UU l1
  place-Petri-Net = type-Finite-Type place-finite-type-Petri-Net

  transition-finite-type-Petri-Net : Finite-Type l2
  transition-finite-type-Petri-Net = pr1 (pr2 P)

  transition-Petri-Net : UU l2
  transition-Petri-Net = type-Finite-Type transition-finite-type-Petri-Net

  incoming-arc-finite-type-Petri-Net :
    place-Petri-Net → transition-Petri-Net → Finite-Type l3
  incoming-arc-finite-type-Petri-Net = pr1 (pr2 (pr2 P))

  incoming-arc-Petri-Net : place-Petri-Net → transition-Petri-Net → UU l3
  incoming-arc-Petri-Net s t =
    type-Finite-Type (incoming-arc-finite-type-Petri-Net s t)

  outgoing-arc-finite-type-Petri-Net :
    transition-Petri-Net → place-Petri-Net → Finite-Type l4
  outgoing-arc-finite-type-Petri-Net = pr2 (pr2 (pr2 P))

  outgoing-arc-Petri-Net : transition-Petri-Net → place-Petri-Net → UU l4
  outgoing-arc-Petri-Net t s =
    type-Finite-Type (outgoing-arc-finite-type-Petri-Net t s)
```

[1]: https://arxiv.org/abs/2005.05108
