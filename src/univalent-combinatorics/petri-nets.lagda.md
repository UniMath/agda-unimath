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
  Σ ( 𝔽 l1)
    ( λ S →
      Σ ( 𝔽 l2)
        ( λ T →
          ( type-𝔽 S → type-𝔽 T → 𝔽 l3) ×
          ( type-𝔽 T → type-𝔽 S → 𝔽 l4)))

module _
  {l1 l2 l3 l4 : Level} (P : Petri-Net l1 l2 l3 l4)
  where

  place-Petri-Net-𝔽 : 𝔽 l1
  place-Petri-Net-𝔽 = pr1 P

  place-Petri-Net : UU l1
  place-Petri-Net = type-𝔽 place-Petri-Net-𝔽

  transition-Petri-Net-𝔽 : 𝔽 l2
  transition-Petri-Net-𝔽 = pr1 (pr2 P)

  transition-Petri-Net : UU l2
  transition-Petri-Net = type-𝔽 transition-Petri-Net-𝔽

  incoming-arc-Petri-Net-𝔽 : place-Petri-Net → transition-Petri-Net → 𝔽 l3
  incoming-arc-Petri-Net-𝔽 = pr1 (pr2 (pr2 P))

  incoming-arc-Petri-Net : place-Petri-Net → transition-Petri-Net → UU l3
  incoming-arc-Petri-Net s t = type-𝔽 (incoming-arc-Petri-Net-𝔽 s t)

  outgoing-arc-Petri-Net-𝔽 : transition-Petri-Net → place-Petri-Net → 𝔽 l4
  outgoing-arc-Petri-Net-𝔽 = pr2 (pr2 (pr2 P))

  outgoing-arc-Petri-Net : transition-Petri-Net → place-Petri-Net → UU l4
  outgoing-arc-Petri-Net t s = type-𝔽 (outgoing-arc-Petri-Net-𝔽 t s)
```

[1]: https://arxiv.org/abs/2005.05108
