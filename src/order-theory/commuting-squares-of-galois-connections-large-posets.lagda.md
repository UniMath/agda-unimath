# Commuting squares of galois connections between large posets

```agda
module order-theory.commuting-squares-of-galois-connections-large-posets where
```

<details><summary>Imports</summary>

```agda

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
