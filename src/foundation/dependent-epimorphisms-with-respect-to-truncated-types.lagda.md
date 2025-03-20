# Dependent epimorphisms with respect to truncated types

```agda
open import foundation.function-extensionality-axiom

module
  foundation.dependent-epimorphisms-with-respect-to-truncated-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.epimorphisms-with-respect-to-truncated-types funext
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.precomposition-dependent-functions
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A **dependent `k`-epimorphism** is a map `f : A → B` such that the
[precomposition function](foundation.precomposition-dependent-functions.md)

```text
  - ∘ f : ((b : B) → C b) → ((a : A) → C (f a))
```

is an [embedding](foundation-core.embeddings.md) for every family `C` of
[`k`-types](foundation.truncated-types.md) over `B`.

Clearly, every dependent `k`-epimorphism is a
[`k`-epimorphism](foundation.epimorphisms-with-respect-to-truncated-types.md).
The converse is also true, i.e., every `k`-epimorphism is a dependent
`k`-epimorphism. Therefore it follows that a map `f : A → B` is
[`k`-acyclic](synthetic-homotopy-theory.truncated-acyclic-maps.md) if and only
if it is a `k`-epimorphism, if and only if it is a dependent `k`-epimorphism.

## Definitions

### The predicate of being a dependent `k`-epimorphism

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  where

  is-dependent-epimorphism-Truncated-Type : (A → B) → UUω
  is-dependent-epimorphism-Truncated-Type f =
    {l : Level} (C : B → Truncated-Type l k) →
    is-emb (precomp-Π f (λ b → type-Truncated-Type (C b)))
```

## Properties

### Every dependent `k`-epimorphism is a `k`-epimorphism

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-epimorphism-is-dependent-epimorphism-Truncated-Type :
    is-dependent-epimorphism-Truncated-Type k f →
    is-epimorphism-Truncated-Type k f
  is-epimorphism-is-dependent-epimorphism-Truncated-Type e X = e (λ _ → X)
```

The converse of the above, that every `k`-epimorphism is a dependent
`k`-epimorphism, can be found in the file on
[`k`-acyclic maps](synthetic-homotopy-theory.truncated-acyclic-maps.md).

## See also

- [`k`-acyclic maps](synthetic-homotopy-theory.truncated-acyclic-maps.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
