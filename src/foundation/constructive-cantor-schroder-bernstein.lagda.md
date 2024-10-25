# The constructive Cantor–Schröder–Bernstein theorem

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module foundation.constructive-cantor-schroder-bernstein where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.complements-subtypes
open import foundation.decidable-embeddings
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import logic.double-negation-stable-embeddings
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
open import order-theory.suplattices
open import order-theory.inflattices
```

</details>

## Idea

The Cantor–Schröder–Bernstein theorem asserts that, assuming
[the law of excluded middle](foundation.law-of-excluded-middle.md), every pair
of mutually [embedding](foundation-core.embeddings.md) types `f : X ↪ Y` and
`g : Y ↪ X` are equivalent. Here, we generalize this statement by dropping the
assumption of the law of excluded middle, and rather considering embeddings that
satisfy certain classicality assumptions.

## Statement

```agda
type-constructive-Cantor-Schröder-Bernstein :
  (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
type-constructive-Cantor-Schröder-Bernstein l1 l2 =
  {X : UU l1} {Y : UU l2} → (X ↪ᵈ Y) → (Y ↪ᵈ X) → X ≃ Y

-- type-constructive-Cantor-Schröder-Bernstein' :
--   (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
-- type-constructive-Cantor-Schröder-Bernstein' l1 l2 =
--   {X : UU l1} {Y : UU l2} → (X ↪ᵈ Y) → (Y ↪ᵈᵐ X) → X ≃ Y
```

## Proof

**Proof.** Let us begin by assuming we have two arbitrary embeddings `f : X ↪ Y`
and `g : Y ↪ X`. In general, these need not be equivalences, so we need to find
a "correction" so that we are left with a pair of mutual inverses.

We will proceed by finding a pair of subtypes that are left fixed by a roundtrip
around taking direct images of `f` and `g` and their complements.

If we begin by considering the entirety of `X` and taking its direct image under
`f`, we are left with a subtype of `Y` that need not be full. By translating to
the complement, we have a measure of "everything that `f` does not hit".
`Y\f(X)`.

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

Using an appropriate fixed point theorem, such as the Knaster–Tarski fixed point
theorem, or Kleene's fixed point theorem, we may deduce that at some point this
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

But this gives us two further fixed points

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
fixed point or that `g` satisfies decidability, only double negation stability.

```agda


module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X ↪ Y)
  where

  hom-half-way-powerset-Cantor-Schröder-Bernstein :
    hom-Large-Poset (λ l3 → l1 ⊔ l2 ⊔ l3)
      ( powerset-Large-Poset X)
      ( opposite-Large-Poset (powerset-Large-Poset Y))
  hom-half-way-powerset-Cantor-Schröder-Bernstein =
    comp-hom-Large-Poset
      ( powerset-Large-Poset X)
      ( powerset-Large-Poset Y)
      ( opposite-Large-Poset (powerset-Large-Poset Y))
      ( neg-hom-powerset)
      ( direct-image-hom-emb-powerset f)

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X ↪ Y) (g : Y ↪ X)
  where

  hom-powerset-Cantor-Schröder-Bernstein :
    hom-Large-Poset
      ( λ l3 → l1 ⊔ l2 ⊔ l3)
      ( powerset-Large-Poset X)
      ( powerset-Large-Poset X)
  hom-powerset-Cantor-Schröder-Bernstein =
    comp-hom-Large-Poset
      ( powerset-Large-Poset X)
      ( opposite-Large-Poset (powerset-Large-Poset Y))
      ( powerset-Large-Poset X)
      ( opposite-hom-Large-Poset
        { P = powerset-Large-Poset Y}
        { opposite-Large-Poset (powerset-Large-Poset X)}
        ( hom-half-way-powerset-Cantor-Schröder-Bernstein g))
      ( hom-half-way-powerset-Cantor-Schröder-Bernstein f)

  hom-small-powerset-Cantor-Schröder-Bernstein :
    (l : Level) →
    hom-Poset
      ( powerset-Poset l X)
      ( powerset-Poset (l1 ⊔ l2 ⊔ l) X)
  hom-small-powerset-Cantor-Schröder-Bernstein =
    hom-poset-hom-Large-Poset
      ( powerset-Large-Poset X)
      ( powerset-Large-Poset X)
      ( hom-powerset-Cantor-Schröder-Bernstein)

```

### Impredicative proof using the Knaster–Tarski fixed point theorem

```text
module _
  {l1 l2 : Level} (resize-prop : propositional-resizing (l1 ⊔ l2) (l1 ⊔ l2))
  {X : UU l1} {Y : UU l2} (f : X ↪ Y) (g : Y ↪ X)
  where

  fixed-point-domain-Cantor-Schröder-Bernstein :
    fixed-point {!   !}
      -- ( map-hom-Poset
      --   ( powerset-Poset (l1 ⊔ l2) X)
      --   ( powerset-Poset (l1 ⊔ l2) X)
      --   ( hom-small-powerset-Cantor-Schröder-Bernstein f g (l1 ⊔ l2)))
  fixed-point-domain-Cantor-Schröder-Bernstein =
    fixed-point-knaster-tarski-Suplattice
      ( resize-type-Suplattice (powerset-Suplattice X {!   !} {!   !}) {!   !}) {!   !} {!   !}
```

Since the fixed point is an image of `g` by double negation stability, it must
be decidable.

```text
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X ↪ Y) (g : Y ↪¬¬ X)
  (S :
    fixed-point
      ( map-hom-Poset
        ( powerset-Poset (l1 ⊔ l2) X)
        ( powerset-Poset (l1 ⊔ l2) X)
        ( hom-small-powerset-Cantor-Schröder-Bernstein f g (l1 ⊔ l2))))
  where

  is-decidable-subtype-fixed-point-Cantor-Schröder-Bernstein :
    is-decidable-subtype S

  map-impredicative-Cantor-Schröder-Bernstein : X → Y
```

We can define mutual inverse maps from the given fixed point. For the inverse
map we need decidability of `f`.

```text
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X ↪ᵈ Y) (g : Y ↪¬¬ X)
  (S :
    fixed-point
      ( map-hom-Poset
        ( powerset-Poset (l1 ⊔ l2) X)
        ( powerset-Poset (l1 ⊔ l2) X)
        ( hom-small-powerset-Cantor-Schröder-Bernstein f g (l1 ⊔ l2))))
  where


  map-inv-impredicative-Cantor-Schröder-Bernstein : Y → X

  is-section-map-inv-impredicative-Cantor-Schröder-Bernstein :
    is-section
      map-impredicative-Cantor-Schröder-Bernstein
      map-inv-impredicative-Cantor-Schröder-Bernstein

  is-retraction-map-inv-impredicative-Cantor-Schröder-Bernstein :
    is-retraction
      map-impredicative-Cantor-Schröder-Bernstein
      map-inv-impredicative-Cantor-Schröder-Bernstein

  is-equiv-map-impredicative-Cantor-Schröder-Bernstein :
    is-equiv map-impredicative-Cantor-Schröder-Bernstein
  is-equiv-map-impredicative-Cantor-Schröder-Bernstein =
    is-equiv-is-invertible
      map-inv-impredicative-Cantor-Schröder-Bernstein
      is-section-map-inv-impredicative-Cantor-Schröder-Bernstein
      is-retraction-map-inv-impredicative-Cantor-Schröder-Bernstein
```

### Proof using Kleene's fixed point theorem

Assuming that `g` is a De Morgan embedding, the operator
`¬X\g(Y\f(-)) : 𝒫(X) → 𝒫(X)` is Scott continuous:

```text
  X\g(Y\f(⋃ᵢUᵢ)) = X\g(Y\(⋃ᵢfᵢ(Uᵢ)))   unions commute with images
                 = X\g(⋂ᵢY\f(Uᵢ))      constructively valid De Morgan law
                 = X\(⋂ᵢg(Y\f(Uᵢ)))    meets commute with images
                 = ⋃ᵢ(X\g(Y\f(Uᵢ)))    g is De Morgan
```

Kleene's fixed point theorem then states that, given a starting point
`U : 𝒫(X)`, the sequence

```text
  ⋃(n : ℕ), (X\gY\f)ⁿ(U)
```

converges to a fixed point `S` of the operator.

Now, again since `g` is De Morgan, every subtype of `Y` gives a decomposition of
`X`, in particular, applying it to `S`:

```text
  X ≅ X\g(Y\f(S)) ∪ X\X\g(Y\f(S)) = S ∪ X\S.
```

In other words, `S` is a decidable subtype of `X`.
