# Nontrivial rings

```agda
module ring-theory.nontrivial-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.invertible-elements-rings
open import ring-theory.rings
open import ring-theory.trivial-rings
```

</details>

## Idea

{{#concept "Nontrivial rings" Agda=is-nontrivial-Ring}} are
[rings](ring-theory.rings.md) in which `0 ≠ 1`.

## Definition

```agda
is-nontrivial-ring-Prop : {l : Level} → Ring l → Prop l
is-nontrivial-ring-Prop R =
  neg-Prop (is-trivial-ring-Prop R)

is-nontrivial-Ring : {l : Level} → Ring l → UU l
is-nontrivial-Ring R = type-Prop (is-nontrivial-ring-Prop R)

is-prop-is-nontrivial-Ring :
  {l : Level} (R : Ring l) → is-prop (is-nontrivial-Ring R)
is-prop-is-nontrivial-Ring R = is-prop-type-Prop (is-nontrivial-ring-Prop R)
```

## Properties

### Invertible elements of nontrivial rings are not equal to zero

```agda
module _
  {l : Level} (R : Ring l) (H : is-nontrivial-Ring R) (x : type-Ring R)
  where

  is-nonzero-is-invertible-element-nontrivial-Ring :
    is-invertible-element-Ring R x → zero-Ring R ≠ x
  is-nonzero-is-invertible-element-nontrivial-Ring (y , P , _) K =
    H ( ( inv (left-zero-law-mul-Ring R y)) ∙
        ( ap (mul-Ring' R y) K) ∙
        ( P))
```
