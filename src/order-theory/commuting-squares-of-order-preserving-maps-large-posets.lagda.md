# Commuting squares of order preserving maps of large posets

```agda
module
  order-theory.commuting-squares-of-order-preserving-maps-large-posets
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps

open import order-theory.large-posets
open import order-theory.order-preserving-maps-large-posets
open import order-theory.similarity-of-order-preserving-maps-large-posets
```

</details>

## Idea

A square

```text
        i
    P -----> U
    |        |
  f |        | g
    ∨        ∨
    Q -----> V
        j
```

of [order preserving maps](order-theory.order-preserving-maps-large-posets.md)
between [large posets](order-theory.large-posets.md) is said to **commute** if
for each `x : type-Large-Poset P l` the elements

```text
  j (f x) : type-Large-Poset V (γj (γf l))
  g (i x) : type-Large-Poset V (γg (γi l))
```

are [similar](order-theory.similarity-of-elements-large-posets.md). In other
words, we say that the square above commutes if the composites `j ∘ f` and
`g ∘ i` are
[similar](order-theory.similarity-of-order-preserving-maps-large-posets.md).

## Definitions

```agda
module _
  {αP αQ αU αV γi γf γg γj : Level → Level}
  {βP βQ βU βV : Level → Level → Level}
  (P : Large-Poset αP βP)
  (Q : Large-Poset αQ βQ)
  (U : Large-Poset αU βU)
  (V : Large-Poset αV βV)
  (i : hom-Large-Poset γi P U)
  (f : hom-Large-Poset γf P Q)
  (g : hom-Large-Poset γg U V)
  (j : hom-Large-Poset γj Q V)
  where

  coherence-square-hom-Large-Poset : UUω
  coherence-square-hom-Large-Poset =
    sim-hom-Large-Poset P V
      ( comp-hom-Large-Poset P Q V j f)
      ( comp-hom-Large-Poset P U V g i)
```
