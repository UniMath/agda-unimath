# Comma types

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.comma-types
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.pullbacks
open import foundation.standard-pullbacks
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import simplicial-type-theory.arrows I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval-type I
```

</details>

## Idea

Given a [span diagram of types](foundation.span-diagrams.md)
`f : B → A ← C : g`, then the
{{#concept "comma type" Disambiguation="in simplicial type theory" Agda=_↓▵_}}
`f ↓▵ g` is the [collection](foundation.dependent-pair-types.md) of
[pairs](foundation.cartesian-product-types.md) of elements `(b , c) : B × C`
[equipped](foundation.structure.md) with a
[directed edge](simplicial-type-theory.directed-edges.md) `f b →▵ g c`.

## Definitions

### The standard comma type

```agda
comma▵ :
  {l1 l2 l3 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} →
  (B → A) → (C → A) → UU (I1 ⊔ l1 ⊔ l2 ⊔ l3)
comma▵ {B = B} {C} f g =
  Σ B (λ b → Σ C (λ c → hom▵ (f b) (g c)))

infix 20 _↓▵_

_↓▵_ :
  {l1 l2 l3 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} →
  (B → A) → (C → A) → UU (I1 ⊔ l1 ⊔ l2 ⊔ l3)
_↓▵_ = comma▵
```

## Properties

### The universal property of the comma type

The comma type `f ↓▵ g` is the pullback of the following diagram

```text
  f ↓▵ g --------> A^Δ¹
    | ⌟             |
    |               | (source , target)
    ∨               ∨
  B × C --------> A × A.
          f × g
```

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B → A) (g : C → A)
  where

  cone-comma▵ :
    cone
      {A = B × C} {Δ¹ → A} {A × A}
      ( λ (b , c) → (f b , g c))
      ( λ α → (α 0▵ , α 1▵))
      ( f ↓▵ g)
  pr1 (cone-comma▵) (b , c , _) =
    (b , c)
  pr1 (pr2 (cone-comma▵)) (_ , _ , α , _) =
    α
  pr2 (pr2 (cone-comma▵)) (_ , _ , _ , α0＝fb , α1＝gc) =
    inv (eq-pair α0＝fb α1＝gc)

  gap-comma▵ :
    f ↓▵ g → standard-pullback (λ (b , c) → (f b , g c)) (λ α → α 0▵ , α 1▵)
  gap-comma▵ =
    gap
      ( λ (b , c) → (f b , g c))
      ( λ α → (α 0▵ , α 1▵))
      ( cone-comma▵)

  map-inv-gap-comma▵ :
    ( standard-pullback
      {A = B × C} {Δ¹ → A} {A × A}
      ( λ (b , c) → (f b , g c))
      ( λ α → α 0▵ , α 1▵)) →
    f ↓▵ g
  map-inv-gap-comma▵ ((b , c) , α , coh) =
    ( b , c , α , pair-eq (inv coh))

  is-section-gap-comma▵ :
    map-inv-gap-comma▵ ∘ gap-comma▵ ~ id
  is-section-gap-comma▵ (b , c , α , coh) =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( eq-pair-eq-fiber
          ( ap pair-eq (inv-inv (eq-pair' coh)) ∙ is-retraction-pair-eq coh)))

  is-retraction-gap-comma▵ :
    gap-comma▵ ∘ map-inv-gap-comma▵ ~ id
  is-retraction-gap-comma▵ ((b , c) , α , coh) =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( ap inv (is-section-pair-eq (inv coh)) ∙ inv-inv coh))

  is-pullback-comma▵ :
    is-pullback
      ( λ (b , c) → (f b , g c))
      ( λ α → (α 0▵ , α 1▵))
      ( cone-comma▵)
  is-pullback-comma▵ =
    is-equiv-is-invertible
      ( map-inv-gap-comma▵)
      ( is-retraction-gap-comma▵)
      ( is-section-gap-comma▵)
```

## References

{{#bibliography}} {{#reference BW23}}
