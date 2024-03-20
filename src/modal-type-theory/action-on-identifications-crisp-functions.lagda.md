# The action on identifications of crisp functions

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.action-on-identifications-crisp-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.identity-types

open import modal-type-theory.crisp-identity-types
```

</details>

## Idea

A function defined on [crisp elements](modal-type-theory.crisp-types.md)
`f : @♭ A → B` preserves crisp
[identifications](foundation-core.identity-types.md), in the sense that it maps
a crisp identification `p : x ＝ y` in `A` to an identification
`crisp-ap f p : f x ＝ f y` in `B`. This action on identifications can be
understood as crisp functoriality of crisp identity types.

This is a strengthening of the
[action on identifications of functions](foundation.action-on-identifications-functions.md)
for crisp identifications, because the function `f : A → B` is allowed to be
defined over only crisp elements of its domain.

## Definition

### The functorial action of functions on crisp identity types

```agda
crisp-ap :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} {B : UU l2} (f : @♭ A → B)
  {@♭ x y : A} → @♭ (x ＝ y) → f x ＝ f y
crisp-ap f refl = refl
```

## Properties

### The identity function acts trivially on identifications

```agda
crisp-ap-id :
  {@♭ l : Level} {@♭ A : UU l} {@♭ x y : A} (@♭ p : x ＝ y) →
  crisp-ap (λ x → x) p ＝ p
crisp-ap-id p = crisp-based-ind-Id (λ y p → crisp-ap (λ x → x) p ＝ p) refl p
```

### The action on identifications of a composite function is the composite of the actions

```agda
crisp-ap-comp :
  {@♭ l1 l2 l3 : Level} {@♭ A : UU l1} {@♭ B : UU l2} {@♭ C : UU l3}
  (@♭ g : @♭ B → C) (@♭ f : @♭ A → B) {@♭ x y : A} (@♭ p : x ＝ y) →
  crisp-ap (λ x → g (f x)) p ＝ crisp-ap g (crisp-ap f p)
crisp-ap-comp g f {x} =
  crisp-based-ind-Id
    ( λ y p → crisp-ap (λ x → g (f x)) p ＝ crisp-ap g (crisp-ap f p))
    ( refl)

crisp-ap-comp-assoc :
  {@♭ l1 l2 l3 l4 : Level}
  {@♭ A : UU l1} {@♭ B : UU l2} {@♭ C : UU l3} {@♭ D : UU l4}
  (@♭ h : @♭ C → D) (@♭ g : B → C) (@♭ f : @♭ A → B)
  {@♭ x y : A} (@♭ p : x ＝ y) →
  crisp-ap (λ z → h (g z)) (crisp-ap f p) ＝
  crisp-ap h (crisp-ap (λ z → g (f z)) p)
crisp-ap-comp-assoc h g f =
  crisp-based-ind-Id
    ( λ y p →
      crisp-ap (λ z → h (g z)) (crisp-ap f p) ＝
      crisp-ap h (crisp-ap (λ z → g (f z)) p))
    ( refl)
```

### The action on identifications of any map preserves `refl`

```agda
crisp-ap-refl :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} {B : UU l2}
  (f : @♭ A → B) (@♭ x : A) →
  crisp-ap f (refl {x = x}) ＝ refl
crisp-ap-refl f x = refl
```

### The action on identifications of any map preserves concatenation of identifications

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2} (@♭ f : @♭ A → B)
  where

  crisp-ap-concat :
    {@♭ x y z : A} (@♭ p : x ＝ y) (@♭ q : y ＝ z) →
    crisp-ap f (p ∙ q) ＝ crisp-ap f p ∙ crisp-ap f q
  crisp-ap-concat p =
    crisp-based-ind-Id
      ( λ z q → crisp-ap f (p ∙ q) ＝ crisp-ap f p ∙ crisp-ap f q)
      (crisp-ap (crisp-ap f) right-unit ∙ inv right-unit)

  crisp-compute-right-refl-ap-concat :
    {@♭ x y : A} (@♭ p : x ＝ y) →
    crisp-ap-concat p refl ＝ crisp-ap (crisp-ap f) right-unit ∙ inv right-unit
  crisp-compute-right-refl-ap-concat p =
    compute-crisp-based-ind-Id
      ( λ z q → crisp-ap f (p ∙ q) ＝ crisp-ap f p ∙ crisp-ap f q)
      (crisp-ap (crisp-ap f) right-unit ∙ inv right-unit)
```

### The action on identifications of any map preserves inverses

```agda
crisp-ap-inv :
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  (@♭ f : @♭ A → B) {@♭ x y : A} (@♭ p : x ＝ y) →
  crisp-ap f (inv p) ＝ inv (crisp-ap f p)
crisp-ap-inv f =
  crisp-based-ind-Id
    ( λ y p → crisp-ap f (inv p) ＝ inv (crisp-ap f p))
    ( refl)
```

### The action on identifications of a constant map is constant

```agda
crisp-ap-const :
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2} (@♭ b : B) {@♭ x y : A}
  (@♭ p : x ＝ y) → crisp-ap (λ _ → b) p ＝ refl
crisp-ap-const b =
  crisp-based-ind-Id (λ y p → crisp-ap (λ _ → b) p ＝ refl) (refl)
```
