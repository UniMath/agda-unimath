# Regular cd-structures

```agda
module orthogonal-factorization-systems.regular-cd-structures where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

A {{#concept "regular cd-structure"}} is a
[cd-structure](orthogonal-factorization-systems.cd-structures.md) which
satisfies the following three axioms:

1. Every distinguished square is [cartesian](foundation.pullbacks.md).
2. The codomain of every distinguished square is an
   [embedding](foundation.embeddings.md).
3. The [diagonal](foundation.diagonals-of-morphisms-arrows.md) of every
   distinguished square
   ```text
         Δ i
      A ─────> A ×_X A
      │           │
    f │           │ functoriality Δ g
      ∨           ∨
      B ─────> B ×_Y B.
         Δ j
   ```
   is again a distinguished square.
