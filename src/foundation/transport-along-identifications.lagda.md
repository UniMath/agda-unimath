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
open import foundation.homotopies
open import foundation.path-algebra
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
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

## Definitions

### The action on identifications of transport

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A} {p p' : x ＝ y}
  where

  tr² : (B : A → UU l2) (α : p ＝ p') (b : B x) → (tr B p b) ＝ (tr B p' b)
  tr² B α b = ap (λ t → tr B t b) α

module _
  {l1 l2 : Level} {A : UU l1} {x y : A} {p p' : x ＝ y}
  {α α' : p ＝ p'}
  where

  tr³ : (B : A → UU l2) (β : α ＝ α') (b : B x) → (tr² B α b) ＝ (tr² B α' b)
  tr³ B β b = ap (λ t → tr² B t b) β
```

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

### Coherences and algebraic identities for `tr²`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A}
  {B : A → UU l2}
  where

  tr²-concat :
    {p p' p'' : x ＝ y} (α : p ＝ p') (α' : p' ＝ p'') (b : B x) →
    (tr² B (α ∙ α') b) ＝ (tr² B α b ∙ tr² B α' b)
  tr²-concat α α' b = ap-concat (λ t → tr B t b) α α'

module _
  {l1 l2 : Level} {A : UU l1} {x y z : A}
  {B : A → UU l2}
  where

  tr²-left-whisk :
    (p : x ＝ y) {q q' : y ＝ z} (β : q ＝ q') (b : B x) →
    coherence-square-identifications
      ( tr² B (identification-left-whisk p β) b)
      ( tr-concat p q' b)
      ( tr-concat p q b)
      ( htpy-right-whisk (tr² B β) (tr B p) b)
  tr²-left-whisk refl refl b = refl

  tr²-right-whisk :
    {p p' : x ＝ y} (α : p ＝ p') (q : y ＝ z) (b : B x) →
    coherence-square-identifications
      ( tr² B (identification-right-whisk α q) b)
      ( tr-concat p' q b)
      ( tr-concat p q b)
      ( htpy-left-whisk (tr B q) (tr² B α) b)
  tr²-right-whisk refl refl b = inv right-unit
```

#### Coherences and algebraic identities for `tr³`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y z : A}
  {B : A → UU l2}
  where

  tr³-htpy-swap-path-swap :
    {q q' : y ＝ z} (β : q ＝ q') {p p' : x ＝ y} (α : p ＝ p') (b : B x) →
    coherence-square-identifications
      ( identification-right-whisk
        ( tr³
          ( B)
          ( path-swap-nat-identification-left-whisk β α)
          ( b))
        ( tr-concat p' q' b))
      ( ( identification-right-whisk
          ( tr²-concat
            ( identification-right-whisk α q)
            ( identification-left-whisk p' β) b)
          ( tr-concat p' q' b)) ∙
      ( vertical-concat-square
        ( tr² B (identification-right-whisk α q) b)
        ( tr² B (identification-left-whisk p' β) b)
        ( tr-concat p' q' b)
        ( tr-concat p' q b)
        ( tr-concat p q b)
        ( htpy-left-whisk (tr B q) (tr² B α) b)
        ( htpy-right-whisk (tr² B β) (tr B p') b)
        ( tr²-right-whisk α q b)
        ( tr²-left-whisk p' β b)))
      ( ( identification-right-whisk
          ( tr²-concat (identification-left-whisk p β)
          ( identification-right-whisk α q') b)
          ( tr-concat p' q' b)) ∙
      ( vertical-concat-square
        ( tr² B (identification-left-whisk p β) b)
        ( tr² B (identification-right-whisk α q') b)
        ( tr-concat p' q' b)
        ( tr-concat p q' b)
        ( tr-concat p q b)
        ( htpy-right-whisk (tr² B β) (tr B p) b)
        ( htpy-left-whisk (tr B q') (tr² B α) b)
        ( tr²-left-whisk p β b)
        ( tr²-right-whisk α q' b)))
      ( identification-left-whisk
        ( tr-concat p q b)
        ( htpy-swap-nat-right-htpy (tr² B β) (tr² B α) b))
  tr³-htpy-swap-path-swap {q = refl} refl {p = refl} refl b = refl
```
