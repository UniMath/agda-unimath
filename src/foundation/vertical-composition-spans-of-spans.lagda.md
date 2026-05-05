# Vertical composition of spans of spans

```agda
module foundation.vertical-composition-spans-of-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-maps
open import foundation.composition-spans
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-spans
open import foundation.homotopies
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.morphisms-spans
open import foundation.pullbacks
open import foundation.spans
open import foundation.spans-of-spans
open import foundation.standard-pullbacks
open import foundation.type-arithmetic-standard-pullbacks
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equivalences-arrows
open import foundation-core.function-types
```

</details>

## Idea

Given three [spans](foundation.spans.md) `F`, `G` and `H` from `A` to `B`, a
[span of spans](foundation.spans-of-spans.md) `α` from `F` to `G` and a span of
spans `β` from `G` to `H`

```text
         F₀
      /  ↑  \
     /   α₀  \
    ∨    ↓    ∨
  A <--- G₀---> B,
    ∧    ↑    ∧
     \   β₀  /
      \  ↓  /
         H₀
```

then we may
{{#concept "vertically compose" Disambiguation="spans of spans of types" Agda=vertical-comp-span-of-spans}}
the two spans of spans to obtain a span of spans `β ∘ α` from `F` to `H`. The
underlying span of the vertical composite is given by the composition of the
underlying spans.

## Definitions

### Vertical composition of spans of spans

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level} {A : UU l1} {B : UU l2}
  (F : span l3 A B) (G : span l4 A B) (H : span l5 A B)
  (β : span-of-spans l6 G H) (α : span-of-spans l7 F G)
  where

  spanning-type-vertical-comp-span-of-spans : UU (l4 ⊔ l6 ⊔ l7)
  spanning-type-vertical-comp-span-of-spans =
    spanning-type-comp-span
      ( span-span-of-spans G H β)
      ( span-span-of-spans F G α)

  left-map-vertical-comp-span-of-spans :
    spanning-type-vertical-comp-span-of-spans → spanning-type-span F
  left-map-vertical-comp-span-of-spans =
    left-map-comp-span
      ( span-span-of-spans G H β)
      ( span-span-of-spans F G α)

  right-map-vertical-comp-span-of-spans :
    spanning-type-vertical-comp-span-of-spans → spanning-type-span H
  right-map-vertical-comp-span-of-spans =
    right-map-comp-span
      ( span-span-of-spans G H β)
      ( span-span-of-spans F G α)

  span-vertical-comp-span-of-spans :
    span (l4 ⊔ l6 ⊔ l7) (spanning-type-span F) (spanning-type-span H)
  span-vertical-comp-span-of-spans =
    comp-span (span-span-of-spans G H β) (span-span-of-spans F G α)

  coherence-left-vertical-comp-span-of-spans :
    coherence-left-span-of-spans F H span-vertical-comp-span-of-spans
  coherence-left-vertical-comp-span-of-spans =
    homotopy-reasoning
      ( left-map-span H ∘
        right-map-span-of-spans G H β ∘
        horizontal-map-standard-pullback)
    ~ ( left-map-span G ∘
        left-map-span-of-spans G H β ∘
        horizontal-map-standard-pullback)
    by coh-left-span-of-spans G H β ·r horizontal-map-standard-pullback
    ~ ( left-map-span G ∘
        right-map-span-of-spans F G α ∘
        vertical-map-standard-pullback)
    by left-map-span G ·l inv-htpy coherence-square-standard-pullback
    ~ ( left-map-span F ∘
        left-map-span-of-spans F G α ∘
        vertical-map-standard-pullback)
    by coh-left-span-of-spans F G α ·r vertical-map-standard-pullback

  coherence-right-vertical-comp-span-of-spans :
    coherence-right-span-of-spans F H span-vertical-comp-span-of-spans
  coherence-right-vertical-comp-span-of-spans =
    homotopy-reasoning
      ( right-map-span H ∘
        right-map-span-of-spans G H β ∘
        horizontal-map-standard-pullback)
    ~ ( right-map-span G ∘
        left-map-span-of-spans G H β ∘
        horizontal-map-standard-pullback)
    by coh-right-span-of-spans G H β ·r horizontal-map-standard-pullback
    ~ ( right-map-span G ∘
        right-map-span-of-spans F G α ∘
        vertical-map-standard-pullback)
    by right-map-span G ·l inv-htpy coherence-square-standard-pullback
    ~ ( right-map-span F ∘
        left-map-span-of-spans F G α ∘
        vertical-map-standard-pullback)
    by coh-right-span-of-spans F G α ·r vertical-map-standard-pullback

  coherence-vertical-comp-span-of-spans :
    coherence-span-of-spans F H span-vertical-comp-span-of-spans
  coherence-vertical-comp-span-of-spans =
    coherence-left-vertical-comp-span-of-spans ,
    coherence-right-vertical-comp-span-of-spans

  vertical-comp-span-of-spans : span-of-spans (l4 ⊔ l6 ⊔ l7) F H
  vertical-comp-span-of-spans =
    span-vertical-comp-span-of-spans , coherence-vertical-comp-span-of-spans
```

## Properties

### Associativity of vertical composition of spans of spans

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level} {A : UU l1} {B : UU l2}
  (F : span l3 A B) (G : span l4 A B) (H : span l5 A B) (I : span l6 A B)
  (γ : span-of-spans l7 H I)
  (β : span-of-spans l8 G H)
  (α : span-of-spans l9 F G)
  where

  essentially-associative-spanning-type-vertical-comp-span-of-spans :
    spanning-type-vertical-comp-span-of-spans F G I
      ( vertical-comp-span-of-spans G H I γ β)
      ( α) ≃
    spanning-type-vertical-comp-span-of-spans F H I
      ( γ)
      ( vertical-comp-span-of-spans F G H β α)
  essentially-associative-spanning-type-vertical-comp-span-of-spans =
    essentially-associative-spanning-type-comp-span
      ( span-span-of-spans H I γ)
      ( span-span-of-spans G H β)
      ( span-span-of-spans F G α)

  essentially-associative-span-vertical-comp-span-of-spans :
    equiv-span
      ( span-vertical-comp-span-of-spans F G I
        ( vertical-comp-span-of-spans G H I γ β)
        ( α))
      ( span-vertical-comp-span-of-spans F H I
        ( γ)
        ( vertical-comp-span-of-spans F G H β α))
  essentially-associative-span-vertical-comp-span-of-spans =
    essentially-associative-comp-span
      ( span-span-of-spans H I γ)
      ( span-span-of-spans G H β)
      ( span-span-of-spans F G α)
```

> It remains to show that this equivalence is part of an equivalence of spans of
> spans.
