# Trivial rings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory.trivial-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.dependent-products-propositions funext
open import foundation.identity-types funext
open import foundation.negated-equality funext univalence truncations
open import foundation.negation funext
open import foundation.propositions funext univalence
open import foundation.sets funext univalence
open import foundation.universe-levels

open import ring-theory.invertible-elements-rings funext univalence truncations
open import ring-theory.rings funext univalence truncations
```

</details>

## Idea

Trivial rings are rings in which `0 = 1`.

## Definition

```agda
is-trivial-ring-Prop : {l : Level} → Ring l → Prop l
is-trivial-ring-Prop R =
  Id-Prop (set-Ring R) (zero-Ring R) (one-Ring R)

is-trivial-Ring : {l : Level} → Ring l → UU l
is-trivial-Ring R = type-Prop (is-trivial-ring-Prop R)

is-prop-is-trivial-Ring :
  {l : Level} (R : Ring l) → is-prop (is-trivial-Ring R)
is-prop-is-trivial-Ring R = is-prop-type-Prop (is-trivial-ring-Prop R)

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

### The carrier type of a trivial ring is contractible

```agda
is-contr-is-trivial-Ring :
  {l : Level} (R : Ring l) →
  is-trivial-Ring R →
  is-contr (type-Ring R)
pr1 (is-contr-is-trivial-Ring R p) = zero-Ring R
pr2 (is-contr-is-trivial-Ring R p) x =
  equational-reasoning
    zero-Ring R
      ＝ mul-Ring R (zero-Ring R) x
        by inv (left-zero-law-mul-Ring R x)
      ＝ mul-Ring R (one-Ring R) x
        by ap-binary (mul-Ring R) p refl
      ＝ x
        by left-unit-law-mul-Ring R x
```

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
