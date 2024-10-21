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
  {X : UU l1} {Y : UU l2} → (X ↪ᵈ Y) → (Y ↪ᵈ X) → X ≃ Y

type-constructive-Cantor-Schröder-Bernstein-Escardó' :
  (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
type-constructive-Cantor-Schröder-Bernstein-Escardó' l1 l2 =
  {X : UU l1} {Y : UU l2} → (X ↪¬¬ Y) → (Y ↪¬¬ X) → X ≃ Y
```

## Proof

**Proof.** Let us begin by assuming we have two arbitrary embeddings `f : X ↪ Y`
and `g : Y ↪ X`. In general, these need not be equivalences, so we need to
construct a "correction" so that we are left with a pair of mutual inverses.

We will proceed by finding a pair of subtypes that are left fixed by a roundtrip
around taking direct images of `f` and `g` and their complements. If we begin by
considering the entirety of `X` and taking its direct image under `f`, we are
left with a subtype of `Y` that need not be full. By translating to the
complement, we have a close measure of "everything that `f` does not hit. This
is what we need to correct for...

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

appropriate fixed point theorems, such as the Knaster–Tarski fixed point
theorem, or Adamek's fixed point theorem?, says that at some point this
operation stabilizes, giving us a subtype `S ⊆ X` such that

```text
  X\g(Y\f(S)) = S.
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

But this gives us two further fixed points: that satisfies `g(Y\f(T)) = Y\T`.

```text
  Y\f(X\g(Y\f(S))) = Y\f(S)    and    X\g(Y\f(X\g(T))) = X\g(T)
```

So if `S` and `T` are greatest fixed points, we have

```text
  X\g(T) ⊆ S    and    Y\f(S) ⊆ T
```

If `g` is double negation stable we also have the equality

```text
  g(Y\f(S)) = X\S.
```

This gives us an inverse map `g⁻¹ : X\S → Y` and similarly there is an inverse
map `f⁻¹ : Y\T → X`. Now, if `S` and `f(S)` were decidable subtypes, we could
define a new total map `h : X → Y` by

```text
  h(x) = f  (x)  if  x ∈ S
  h(x) = g⁻¹(x)  if  x ∉ S
```

and a converse map

```text
  h'(x) = f⁻¹(x)  if  x ∈ f(S)
  h'(x) = g  (x)  if  x ∉ f(S).
```

Clearly, this gives a pair of mutually inverse maps.

Here we're not using the existence of `T` at all, nor that `S` is a greatest
fixed point or that `g` satisfies any decidability property.

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
