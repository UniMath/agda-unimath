# The constructive Cantor–Schröder–Bernstein-Escardó theorem

```agda
module foundation.constructive-cantor-schroder-bernstein-escardo where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.complements-subtypes
open import foundation.decidable-embeddings
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation-stable-embeddings
open import foundation.fixed-points-endofunctions
open import foundation.images-embeddings
open import foundation.injective-maps
open import foundation.negation
open import foundation.perfect-images
open import foundation.powersets
open import foundation.propositional-maps
open import foundation.propositional-resizing
open import foundation.split-surjective-maps
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.sets

open import order-theory.knaster-tarski-fixed-point-theorem
open import order-theory.opposite-large-posets
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-posets
```

</details>

## Idea

The Cantor–Schröder–Bernstein-Escardó theorem asserts that, assuming
[the law of excluded middle](foundation.law-of-excluded-middle.md), every pair
of mutually [embedding](foundation-core.embeddings.md) types `f : X ↪ Y` and
`g : Y ↪ X` are equivalent. Here, we generalize this statement by dropping the
assumption of the law of excluded middle, and rather consider
[double negation stable embeddings](foundation.double-negation-stable-embeddings.md)
between `X` and `Y`.

## Statement

```agda
type-constructive-Cantor-Schröder-Bernstein-Escardó :
  (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
type-constructive-Cantor-Schröder-Bernstein-Escardó l1 l2 =
  {X : UU l1} {Y : UU l2} → (X ↪¬¬ Y) → (Y ↪¬¬ X) → X ≃ Y
```

## Proof

**Proof.** We begin by observing that given a double negation stable embedding,

```text
  f : X → Y
```

then the image of `f` gives a decomposition of `Y`, `Y ≃ f(X) + Y\f(X) + ε`.

```text
        X                           Y
     _______                     _______
    /       \                   /       \
   /         \                 /         \
  |           |       f       |           |
  |           |   -------->   |    f(X)   |
  |~~~~~~~~~~~|               |           |
  |           |       g       |~~~~~~~~~~~| <-?- Y\(f(X) ∪ Y\f(X))
  | g(Y\f(X)) |   <--------   |           |
  |           |               |   Y\f(X)  |
   \         /                 \         /
    \_______/                   \_______/
```

the ??? fixed point theorem says that at some point this operation stabilizes,
giving us a subtype `S ⊆ X` such that

```text
  X\g(Y\f(S)) = S.
```

By double negation stability we also have the equation

```text
  g(Y\f(S)) = X\S.
```

```text
        X                           Y
     _______                     _______
    /       \                   / f(S)  \
   /         \                 /~~~~~~~~~\ <--- "Y\(f(S) ∪ Y\f(S))"
  |           |       f       |           |
  |           |   -------->   |           |
  |           |               |           |
  |           |       g       |           |
  |           |   <--------   |           |
  |           |               |           |
   \~~~~~~~~~/                 \         /
    \___S___/                   \_______/
```

Dually, we also have a least fixed point `T` of the endooperator

```text
  B ↦ Y\(f(X\g(B)))
```

that satisfies `g(Y\f(T)) = Y\T`. But this gives us two further fixed points:

```text
  X\g(Y\f(X\g(S))) = X\g(S)    and    Y\f(X\g(Y\f(T))) = Y\f(T)
```

If we can prove that `S` and `T` are decidable, then we can finish the proof in
the classical way.

```text
  S ∪ X\S = X\g(Y\f(S)) ∪ g(Y\f(S))
```

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X ↪ Y)
  where

  hom-half-way-powerset-Cantor-Schröder-Bernstein-Escardó :
    hom-Large-Poset (λ l → l2 ⊔ l1 ⊔ l)
      ( powerset-Large-Poset X)
      ( opposite-Large-Poset (powerset-Large-Poset Y))
  hom-half-way-powerset-Cantor-Schröder-Bernstein-Escardó =
    comp-hom-Large-Poset
      ( powerset-Large-Poset X)
      ( powerset-Large-Poset Y)
      ( opposite-Large-Poset (powerset-Large-Poset Y))
      ( neg-hom-powerset)
      ( direct-image-hom-emb-powerset f)

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X ↪ Y) (g : Y ↪ X)
  where

  hom-powerset-Cantor-Schröder-Bernstein-Escardó :
    hom-Large-Poset
      ( λ l3 → l1 ⊔ l2 ⊔ l3)
      ( powerset-Large-Poset X)
      ( powerset-Large-Poset X)
  hom-powerset-Cantor-Schröder-Bernstein-Escardó =
    comp-hom-Large-Poset
      ( powerset-Large-Poset X)
      ( opposite-Large-Poset (powerset-Large-Poset Y))
      ( powerset-Large-Poset X)
      ( opposite-hom-Large-Poset
        { P = powerset-Large-Poset Y}
        { opposite-Large-Poset (powerset-Large-Poset X)}
        ( hom-half-way-powerset-Cantor-Schröder-Bernstein-Escardó g))
      ( hom-half-way-powerset-Cantor-Schröder-Bernstein-Escardó f)
```

### Impredicative proof using the Knaster–Tarski fixed point theorem

TODO
