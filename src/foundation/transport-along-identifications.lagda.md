# Transport along identifications

```agda
module foundation.transport-along-identifications where

open import foundation-core.transport-along-identifications public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

Given a type family `B` over `A`, an
[identification](foundation-core.identity-types.md) `p : x ＝ y` in `A` and an
element `b : B x`, we can
[**transport**](foundation-core.transport-along-identifications.md) the element
`b` along the identification `p` to obtain an element `tr B p b : B y`.

The fact that `tr B p` is an [equivalence](foundation-core.equivalences.md) is
recorded on this page.

## Properties

### Transport is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A}
  where

  is-retraction-inv-tr : (p : x ＝ y) → is-retraction (tr B p) (inv-tr B p)
  is-retraction-inv-tr refl b = refl

  is-section-inv-tr : (p : x ＝ y) → is-section (tr B p) (inv-tr B p)
  is-section-inv-tr refl b = refl

  is-equiv-tr : (p : x ＝ y) → is-equiv (tr B p)
  is-equiv-tr p =
    is-equiv-is-invertible
      ( inv-tr B p)
      ( is-section-inv-tr p)
      ( is-retraction-inv-tr p)

  is-equiv-inv-tr : (p : x ＝ y) → is-equiv (inv-tr B p)
  is-equiv-inv-tr p =
    is-equiv-is-invertible
      ( tr B p)
      ( is-retraction-inv-tr p)
      ( is-section-inv-tr p)

  equiv-tr : x ＝ y → B x ≃ B y
  equiv-tr p = (tr B p , is-equiv-tr p)

  equiv-inv-tr : x ＝ y → B y ≃ B x
  equiv-inv-tr p = (inv-tr B p , is-equiv-inv-tr p)
```

### Transporting along `refl` is the identity equivalence

```agda
equiv-tr-refl :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x : A} →
  equiv-tr B refl ＝ id-equiv {A = B x}
equiv-tr-refl B = refl
```

### Computing transport of loops

```agda
tr-loop :
  {l1 : Level} {A : UU l1} {a0 a1 : A} (p : a0 ＝ a1) (q : a0 ＝ a0) →
  tr (λ y → y ＝ y) p q ＝ (inv p ∙ q) ∙ p
tr-loop refl q = inv right-unit

tr-loop-self :
  {l1 : Level} {A : UU l1} {a : A} (p : a ＝ a) →
  tr (λ y → y ＝ y) p p ＝ p
tr-loop-self p = tr-loop p p ∙ ap (_∙ p) (left-inv p)
```
