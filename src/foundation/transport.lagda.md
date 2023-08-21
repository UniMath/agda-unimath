# Transport

```agda
module foundation.transport where

open import foundation-core.transport public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.path-algebra
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Idea

Given a type family `B` over `A`, an
[identification](foundation-core.identity-types.md) `p : x ＝ y` in `A` and an
element `b : B x`, we can [**transport**](foundation-core.transport.md) the
element `b` along the identification `p` to obtain an element `tr B p b : B y`.

The fact that `tr B p` is an [equivalence](foundation-core.equivalences.md) is
recorded in this file.

## Definitions

### The action on identifications of transport

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} {p0 p1 : a0 ＝ a1}
  where

  tr² : (B : A → UU l2) (α : p0 ＝ p1) (b0 : B a0) → (tr B p0 b0) ＝ (tr B p1 b0)
  tr² B α b0 = ap (λ t → tr B t b0) α

module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} {p0 p1 : a0 ＝ a1}
  {α α' : p0 ＝ p1}
  where

  tr³ : (B : A → UU l2) (β : α ＝ α') (b0 : B a0) → (tr² B α b0) ＝ (tr² B α' b0)
  tr³ B β b0 = ap (λ t → tr² B t b0) β
```

## Properties

### Transport is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A}
  where

  inv-tr : x ＝ y → B y → B x
  inv-tr p = tr B (inv p)

  is-retraction-inv-tr : (p : x ＝ y) → ((inv-tr p) ∘ (tr B p)) ~ id
  is-retraction-inv-tr refl b = refl

  is-section-inv-tr : (p : x ＝ y) → ((tr B p) ∘ (inv-tr p)) ~ id
  is-section-inv-tr refl b = refl

  is-equiv-tr : (p : x ＝ y) → is-equiv (tr B p)
  is-equiv-tr p =
    is-equiv-has-inverse
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
tr-subst :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (B : A → UU l3) (f : X → A)
  {x y : X} (p : x ＝ y) {x' : B (f x)} →
  tr B (ap f p) x' ＝ tr (B ∘ f) p x'
tr-subst B f refl = refl
```

### Coherences and algebraic identities for tr²

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A}
  {B : A → UU l2}
  where

  tr²-concat :
    {p p' p'' : a0 ＝ a1} (α : p ＝ p') (α' : p' ＝ p'') (b0 : B a0) →
    (tr² B (α ∙ α') b0) ＝ (tr² B α b0 ∙ tr² B α' b0)
  tr²-concat α α' b0 = ap-concat (λ t → tr B t b0) α α'

module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 a2 : A}
  {B : A → UU l2}
  where

  tr²-left-whisk :
    (p : a0 ＝ a1) {q q' : a1 ＝ a2} (β : q ＝ q') (b0 : B a0) →
    coherence-square-identifications
      ( tr² B (identification-left-whisk p β) b0)
      ( tr-concat p q' b0)
      ( tr-concat p q b0)
      ( htpy-right-whisk (tr² B β) (tr B p) b0)
  tr²-left-whisk refl refl b0 = refl

  tr²-right-whisk :
    {p p' : a0 ＝ a1} (α : p ＝ p') (q : a1 ＝ a2) (b0 : B a0) →
    coherence-square-identifications
      ( tr² B (identification-right-whisk α q) b0)
      ( tr-concat p' q b0)
      ( tr-concat p q b0)
      ( htpy-left-whisk (tr B q) (tr² B α) b0)
  tr²-right-whisk refl refl b0 = inv right-unit
```

#### Coherences for tr³

```
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 a2 : A}
  {B : A → UU l2}
  where

  tr³-htpy-swap-path-swap :
    {q q' : a1 ＝ a2 } (β : q ＝ q') {p p' : a0 ＝ a1} (α : p ＝ p') (b0 : B a0) →
    coherence-square-identifications
      ( identification-right-whisk (tr³ B (path-swap-nat-identification-left-whisk β α) b0) (tr-concat p' q' b0))
      ( (identification-right-whisk
        ( tr²-concat
          ( identification-right-whisk α q)
          ( identification-left-whisk p' β) b0)
        ( tr-concat p' q' b0)) ∙
      ( vertical-concat-square
        ( tr² B (identification-right-whisk α q) b0)
        ( tr² B (identification-left-whisk p' β) b0)
        ( tr-concat p' q' b0)
        ( tr-concat p' q b0)
        ( tr-concat p q b0)
        ( htpy-left-whisk (tr B q) (tr² B α) b0)
        ( htpy-right-whisk (tr² B β) (tr B p') b0)
        ( tr²-right-whisk α q b0)
        ( tr²-left-whisk p' β b0)))
      ( (identification-right-whisk
        ( tr²-concat (identification-left-whisk p β)
        ( identification-right-whisk α q') b0)
        ( tr-concat p' q' b0)) ∙
      (vertical-concat-square
        ( tr² B (identification-left-whisk p β) b0)
        ( tr² B (identification-right-whisk α q') b0)
        ( tr-concat p' q' b0)
        ( tr-concat p q' b0)
        ( tr-concat p q b0)
        ( htpy-right-whisk (tr² B β) (tr B p) b0)
        ( htpy-left-whisk (tr B q') (tr² B α) b0)
        ( tr²-left-whisk p β b0)
        ( tr²-right-whisk α q' b0)))
      ( identification-left-whisk
        ( tr-concat p q b0)
        ( htpy-swap-nat-right-htpy (tr² B β) (tr² B α) b0))
  tr³-htpy-swap-path-swap {q = refl} refl {p = refl} refl b0 = refl
```
