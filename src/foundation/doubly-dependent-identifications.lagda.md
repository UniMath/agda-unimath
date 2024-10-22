# Doubly dependent identifications

```agda
module foundation.doubly-dependent-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-identifications
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

Consider a family of types `C x y` indexed by `x : A` and `y : B`, and consider [identifications](foundation-core.identity-types.md) `p : x ＝ x'` and `q : y ＝ y'` in `A` and `B`, respectively. A {{#concept "doubly dependent identification" Agda=doubly-dependent-identification}} from `c : C x y` to `c' : C x' y'` over `p` and `q` is a [dependent identification](foundation.dependent-identifications.md)

```text
  r : dependent-identification (C x') p (tr (λ t → C t y) p c) c'
```

## Definitions

### Doubly dependent identifications

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : A → B → UU l3)
  where

  doubly-dependent-identification :
    {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
    C x y → C x' y' → UU l3
  doubly-dependent-identification p q c c' =
    dependent-identification (C _) q (tr (λ u → C u _) p c) c'
```
