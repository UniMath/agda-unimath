# Transport along identifications

```agda
module foundation.transport-along-identifications where

open import foundation-core.transport-along-identifications public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.path-algebra
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

Given a type family `B` over `A`, an
[identification](foundation-core.identity-types.md) `p : x ＝ y` in `A` and an
element `b : B x`, we can
[**transport**](foundation-core.transport-along-identifications.md) the element
`b` along the identification `p` to obtain an element `tr B p b : B y`.

The fact that `tr B p` is an [equivalence](foundation-core.equivalences.md) is
recorded in this file.

## Properties

### Transport is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A}
  where

  inv-tr : x ＝ y → B y → B x
  inv-tr p = tr B (inv p)

  is-retraction-inv-tr : (p : x ＝ y) → (inv-tr p ∘ tr B p) ~ id
  is-retraction-inv-tr refl b = refl

  is-section-inv-tr : (p : x ＝ y) → (tr B p ∘ inv-tr p) ~ id
  is-section-inv-tr refl b = refl

  is-equiv-tr : (p : x ＝ y) → is-equiv (tr B p)
  is-equiv-tr p =
    is-equiv-is-invertible
      ( inv-tr p)
      ( is-section-inv-tr p)
      ( is-retraction-inv-tr p)

  equiv-tr : x ＝ y → (B x) ≃ (B y)
  pr1 (equiv-tr p) = tr B p
  pr2 (equiv-tr p) = is-equiv-tr p
```

### Transporting along `refl` is the identity equivalence

```agda
equiv-tr-refl :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x : A} →
  equiv-tr B refl ＝ id-equiv {A = B x}
equiv-tr-refl B = refl
```

### Substitution law for transport

```agda
substitution-law-tr :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (B : A → UU l3) (f : X → A)
  {x y : X} (p : x ＝ y) {x' : B (f x)} →
  tr B (ap f p) x' ＝ tr (B ∘ f) p x'
substitution-law-tr B f refl = refl
```

### Computing transport in the type family of identifications with a fixed target

```agda
tr-Id-left :
  {l : Level} {A : UU l} {a b c : A} (q : b ＝ c) (p : b ＝ a) →
  tr (_＝ a) q p ＝ ((inv q) ∙ p)
tr-Id-left refl p = refl
```

### Computing transport in the type family of identifications with a fixed source

```agda
tr-Id-right :
  {l : Level} {A : UU l} {a b c : A} (q : b ＝ c) (p : a ＝ b) →
  tr (a ＝_) q p ＝ (p ∙ q)
tr-Id-right refl refl = refl
```

### Computing transport of loops

```agda
tr-loop :
  {l1 : Level} {A : UU l1} {a0 a1 : A} (p : a0 ＝ a1) (l : a0 ＝ a0) →
  (tr (λ y → y ＝ y) p l) ＝ ((inv p ∙ l) ∙ p)
tr-loop refl l = inv right-unit
```
