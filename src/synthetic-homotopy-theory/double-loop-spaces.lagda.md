# Double loop spaces

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory.double-loop-spaces
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications funext
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.path-algebra funext
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation funext

open import structured-types.pointed-equivalences funext univalence truncations
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces funext univalence truncations
open import synthetic-homotopy-theory.iterated-loop-spaces funext univalence truncations
open import synthetic-homotopy-theory.loop-spaces funext univalence truncations
```

</details>

## Idea

The **double loop space** of a [pointed type](structured-types.pointed-types.md)
`A` is the [loop space](synthetic-homotopy-theory.loop-spaces.md) of the loop
space of `A`.

## Definition

```agda
module _
  {l : Level}
  where

  Ω² : Pointed-Type l → Pointed-Type l
  Ω² A = iterated-loop-space 2 A

  type-Ω² : {A : UU l} (a : A) → UU l
  type-Ω² a = refl {x = a} ＝ refl {x = a}

  refl-Ω² : {A : UU l} {a : A} → type-Ω² a
  refl-Ω² = refl
```

### Vertical and horizontal concatenation operations on double loop

spaces.

```agda
vertical-concat-Ω² :
  {l : Level} {A : UU l} {a : A} → type-Ω² a → type-Ω² a → type-Ω² a
vertical-concat-Ω² α β = vertical-concat-Id² α β

horizontal-concat-Ω² :
  {l : Level} {A : UU l} {a : A} → type-Ω² a → type-Ω² a → type-Ω² a
horizontal-concat-Ω² α β = horizontal-concat-Id² α β
```

### Unit laws horizontal, vertical concatenation, and whiskering

```agda
module _
  {l : Level} {A : UU l}
  where

  left-unit-law-vertical-concat-Ω² :
    {a : A} {α : type-Ω² a} → vertical-concat-Ω² refl-Ω² α ＝ α
  left-unit-law-vertical-concat-Ω² = left-unit

  right-unit-law-vertical-concat-Ω² :
    {a : A} {α : type-Ω² a} → vertical-concat-Ω² α refl-Ω² ＝ α
  right-unit-law-vertical-concat-Ω² = right-unit

  left-unit-law-horizontal-concat-Ω² :
    {a : A} {α : type-Ω² a} →
    horizontal-concat-Ω² refl-Ω² α ＝ α
  left-unit-law-horizontal-concat-Ω² {α = α} =
    compute-left-refl-horizontal-concat-Id² α ∙ ap-id α

  naturality-right-unit :
    {x y : A} {p q : x ＝ y} (α : p ＝ q) →
    coherence-square-identifications
      ( right-unit)
      ( right-whisker-concat α refl)
      ( α)
      ( right-unit)
  naturality-right-unit {p = refl} refl = refl

  naturality-right-unit-Ω² :
    {x : A} (α : type-Ω² x) → right-whisker-concat α refl ＝ α
  naturality-right-unit-Ω² α = inv right-unit ∙ naturality-right-unit α

  right-unit-law-horizontal-concat-Ω² :
    {a : A} {α : type-Ω² a} → horizontal-concat-Ω² α refl-Ω² ＝ α
  right-unit-law-horizontal-concat-Ω² {α = α} =
    compute-right-refl-horizontal-concat-Id² α ∙ naturality-right-unit-Ω² α

  left-unit-law-left-whisker-Ω² :
    {a : A} (α : type-Ω² a) → left-whisker-concat (refl-Ω (A , a)) α ＝ α
  left-unit-law-left-whisker-Ω² α =
    left-unit-law-left-whisker-concat α

  right-unit-law-right-whisker-Ω² :
    {a : A} (α : type-Ω² a) → right-whisker-concat α (refl-Ω (A , a)) ＝ α
  right-unit-law-right-whisker-Ω² α =
    inv (right-unit-law-right-whisker-concat α ∙ right-unit)
```

### The interchange law for double loop spaces

```agda
interchange-Ω² :
  {l : Level} {A : UU l} {a : A} (α β γ δ : type-Ω² a) →
  Id
    ( horizontal-concat-Ω² (vertical-concat-Ω² α β) (vertical-concat-Ω² γ δ))
    ( vertical-concat-Ω² (horizontal-concat-Ω² α γ) (horizontal-concat-Ω² β δ))
interchange-Ω² = interchange-Id²
```

## Properties

### The loop space of a pointed type is equivalent to a double loop space

```agda
module _
  {l : Level} (A : Pointed-Type l) {x : type-Pointed-Type A}
  (p : point-Pointed-Type A ＝ x)
  where

  pointed-equiv-2-loop-pointed-identity :
    Ω (point-Pointed-Type A ＝ x , p) ≃∗ Ω² A
  pointed-equiv-2-loop-pointed-identity =
    pointed-equiv-Ω-pointed-equiv (pointed-equiv-loop-pointed-identity A p)
```
