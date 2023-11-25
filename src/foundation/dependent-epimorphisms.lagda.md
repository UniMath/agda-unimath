# Dependent epimorphisms

```agda
module foundation.dependent-epimorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.epimorphisms
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.precomposition-dependent-functions
```

</details>

## Idea

A **dependent epimorphism** is a map `f : A → B` such that the precomposition
function

```text
  - ∘ f : ((b : B) → C b) → ((a : A) → C (f a))
```

is an [embedding](foundation-core.embeddings.md) for every type family `C` over
`B`.

Clearly, every dependent epimorphism is an
[epimorphism](foundation.epimorphisms.md). The converse is also true, i.e.,
every epimorphism is a dependent epimorphism. Therefore it follows that a map
`f : A → B` is [acyclic](synthetic-homotopy-theory.acyclic-maps.md) if and only
if it is an epimorphism, if and only if it is a dependent epimorphism.

## Definitions

### The predicate of being a dependent epimorphism

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-dependent-epimorphism : (A → B) → UUω
  is-dependent-epimorphism f =
    {l : Level} (C : B → UU l) → is-emb (precomp-Π f C)
```

## Properties

### Every dependent epimorphism is an epimorphism

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-epimorphism-is-dependent-epimorphism :
    is-dependent-epimorphism f → is-epimorphism f
  is-epimorphism-is-dependent-epimorphism e X = e (λ _ → X)
```

The converse of the above, that every epimorphism is a dependent epimorphism,
can be found in the file on
[acyclic maps](synthetic-homotopy-theory.acyclic-maps.md).

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
