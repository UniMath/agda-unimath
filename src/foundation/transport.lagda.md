# Transport

```agda
module foundation.transport where

open import foundation-core.transport public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

This file records interactions between transport (`tr`) and other constructions.

## Properties

### Transport is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A}
  where

  inv-tr : x ＝ y → B y → B x
  inv-tr p = tr B (inv p)

  isretr-inv-tr : (p : x ＝ y) → ((inv-tr p) ∘ (tr B p)) ~ id
  isretr-inv-tr refl b = refl

  issec-inv-tr : (p : x ＝ y) → ((tr B p) ∘ (inv-tr p)) ~ id
  issec-inv-tr refl b = refl

  is-equiv-tr : (p : x ＝ y) → is-equiv (tr B p)
  is-equiv-tr p =
    is-equiv-has-inverse
      ( inv-tr p)
      ( issec-inv-tr p)
      ( isretr-inv-tr p)

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

### Transport in identity types

```agda
tr-fx＝gy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {a0 a1 : A} {b0 b1 : B} (f : A → C) (g : B → C)
  (p : a0 ＝ a1) (q : b0 ＝ b1) (s : f a0 ＝ g b0) →
  (tr (λ z → (f (pr1 z)) ＝ (g (pr2 z))) (eq-pair p q) s) ＝
  (((inv (ap f p)) ∙ s) ∙ (ap g q))
tr-fx＝gy f g refl refl s = inv right-unit

tr-x＝y :
  {l1 : Level} {A : UU l1} {a0 a1 a2 a3 : A}
  (p : a0 ＝ a1) (q : a2 ＝ a3) (s : a0 ＝ a2) →
  (tr (λ z → (pr1 z) ＝ (pr2 z)) (eq-pair p q) s) ＝ ((inv p) ∙ (s ∙ q))
tr-x＝y refl refl s = inv right-unit
```

### Transport in the family of loops

```agda
tr-loop :
  {l1 : Level} {A : UU l1} {a0 a1 : A} (p : a0 ＝ a1) (l : a0 ＝ a0) →
  (tr (λ y → y ＝ y) p l) ＝ (((inv p) ∙ l) ∙ p)
tr-loop refl l = inv right-unit
```

### Transport of identifications

```agda
tr-Id :
  {l1 : Level} {A : UU l1} {a0 a1 a2 : A} (p : a1 ＝ a2) (l : a0 ＝ a1) →
  (tr (a0 ＝_) p l) ＝ (l ∙ p)
tr-Id refl refl = refl
```
