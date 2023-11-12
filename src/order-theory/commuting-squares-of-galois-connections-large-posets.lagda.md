# Commuting squares of galois connections between large posets

```agda
module order-theory.commuting-squares-of-galois-connections-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import order-theory.galois-connections-large-posets
open import order-theory.large-posets
```

</details>

## Idea

Consider a diagram of
[Galois connections](order-theory.galois-connections-large-posets.md)

```text
           LI
        ------->
      P     ⊥    U
     |  <-------
     | ∧   UI   | ∧
     | |        | |
  LF | |     LG | |
     |⊣| UF     |⊣| UG
     | |        | |
     ∨ |   LJ   ∨ |
        ------->  |
      Q     ⊥    V.
        <-------
           UJ
```

between large posets. We say that the diagram commutes if there is a
[weak homotopy](order-theory.weak-homotopies-order-preserving-maps-large-posets.md)
`LJ ∘ LF ~ LG ∘ LI`. This condition is equivalent the condition that there is a
weak homotopy `UF ∘ UJ ~ UI ∘ UG`.

By the adjoint relations between the galois connection it also follows that
there are weak homotopies `LI ∘ UF ~ UG ∘ LJ` and `LF ∘ UI ~ UJ ∘ LG`.

## Definitions

### Commuting squares of Galois connections

```agda
module _
  {αP αQ αU αV γF γG γI γJ δF δG δI δJ : Level → Level}
  {βP βQ βU βV : Level → Level → Level}
  (P : Large-Poset αP βP)
  (Q : Large-Poset αQ βQ)
  (U : Large-Poset αU βU)
  (V : Large-Poset αV βV)
  (I : galois-connection-Large-Poset γI δI P U)
  (F : galois-connection-Large-Poset γF δF P Q)
  (G : galois-connection-Large-Poset γG δG U V)
  (J : galois-connection-Large-Poset γJ δJ Q V)
  where

  coherence-square-lower-adjoint-galois-connection-Large-Poset : UUω
  coherence-square-lower-adjoint-galois-connection-Large-Poset =
    weak-htpy-lower-adjoint-galois-connection-Large-Poset P V
      ( comp-galois-connection-Large-Poset P Q V J F)
      ( comp-galois-connection-Large-Poset P U V G I)

  coherence-square-upper-adjoint-galois-connection-Large-Poset : UUω
  coherence-square-upper-adjoint-galois-connection-Large-Poset =
    weak-htpy-upper-adjoint-galois-connection-Large-Poset P V
      ( comp-galois-connection-Large-Poset P U V G I)
      ( comp-galois-connection-Large-Poset P Q V J F)
```
