# Epimorphisms

```agda
module foundation.epimorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.function-types
```

</details>

## Idea

A map `f : A → B` is said to be an **epimorphism** if the precomposition
function

```text
  - ∘ f : (B → X) → (A → X)
```

is an [embedding](foundation-core.embeddings.md) for every type `X`.

## Definitions

```agda
module _
  {l1 l2 : Level} (l : Level) {A : UU l1} {B : UU l2}
  where

  is-epimorphism : (A → B) → UUω
  is-epimorphism f = {l : Level} (X : UU l) → is-emb (precomp f X)
```

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
