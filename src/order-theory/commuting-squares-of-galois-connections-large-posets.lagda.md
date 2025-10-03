# Commuting squares of Galois connections between large posets

```agda
module order-theory.commuting-squares-of-galois-connections-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import order-theory.commuting-squares-of-order-preserving-maps-large-posets
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

between [large posets](order-theory.large-posets.md). We say that the diagram
**commutes** if there is a
[similarity](order-theory.similarity-of-order-preserving-maps-large-posets.md)
`LJ ∘ LF ≍ LG ∘ LI`. This condition is
[equivalent](foundation.logical-equivalences.md) the condition that there is a
similarity `UF ∘ UJ ≍ UI ∘ UG`.

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

  lower-coherence-square-galois-connection-Large-Poset : UUω
  lower-coherence-square-galois-connection-Large-Poset =
    sim-lower-galois-connection-Large-Poset P V
      ( comp-galois-connection-Large-Poset P Q V J F)
      ( comp-galois-connection-Large-Poset P U V G I)

  upper-coherence-square-galois-connection-Large-Poset : UUω
  upper-coherence-square-galois-connection-Large-Poset =
    sim-upper-galois-connection-Large-Poset P V
      ( comp-galois-connection-Large-Poset P U V G I)
      ( comp-galois-connection-Large-Poset P Q V J F)
```

## Properties

### A commuting square of lower adjoints of galois connections induces a commuting square of upper adjoints and vice versa

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

  lower-coherence-square-upper-coherence-square-galois-connection-Large-Poset :
    upper-coherence-square-galois-connection-Large-Poset
      P Q U V I F G J →
    lower-coherence-square-galois-connection-Large-Poset
      P Q U V I F G J
  lower-coherence-square-upper-coherence-square-galois-connection-Large-Poset =
    sim-lower-sim-upper-galois-connection-Large-Poset P V
      ( comp-galois-connection-Large-Poset P Q V J F)
      ( comp-galois-connection-Large-Poset P U V G I)

  upper-coherence-square-lower-coherence-square-galois-connection-Large-Poset :
    lower-coherence-square-galois-connection-Large-Poset
      P Q U V I F G J →
    upper-coherence-square-galois-connection-Large-Poset
      P Q U V I F G J
  upper-coherence-square-lower-coherence-square-galois-connection-Large-Poset =
    sim-upper-sim-lower-galois-connection-Large-Poset P V
      ( comp-galois-connection-Large-Poset P Q V J F)
      ( comp-galois-connection-Large-Poset P U V G I)
```
