# Nilradical of a commutative ring

```agda
module commutative-algebra.nilradical-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.binomial-theorem-commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.sums-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.nilpotent-elements-rings
```

</details>

## Idea

The nilradical of a commutative ring is the ideal consisting of all nilpotent
elements.

## Definitions

```agda
subset-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → subset-Commutative-Ring l R
subset-nilradical-Commutative-Ring R =
  is-nilpotent-element-ring-Prop (ring-Commutative-Ring R)
```

## Properties

### The nilradical is the intersection of all prime ideals

```agda
contains-zero-subset-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  is-in-subtype
    ( subset-nilradical-Commutative-Ring R)
    ( zero-Commutative-Ring R)
contains-zero-subset-nilradical-Commutative-Ring R = intro-∃ 1 refl

```

### The nilradical is closed under addition

```agda
is-closed-under-addition-subset-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) {x y : type-Commutative-Ring R} →
  is-in-subtype (subset-nilradical-Commutative-Ring R) x → 
  is-in-subtype (subset-nilradical-Commutative-Ring R) y →
  is-in-subtype
    ( subset-nilradical-Commutative-Ring R)
    ( add-Commutative-Ring R x y)
is-closed-under-addition-subset-nilradical-Commutative-Ring R {x} {y} f h = 
  apply-universal-property-trunc-Prop f 
    ( subset-nilradical-Commutative-Ring R (add-Commutative-Ring R x y)) 
    ( λ (n , p) → 
      apply-universal-property-trunc-Prop h 
        ( subset-nilradical-Commutative-Ring R (add-Commutative-Ring R x y)) 
        ( λ (m , q) → 
          intro-∃
            ( add-ℕ n m)
            ( ( binomial-theorem-Commutative-Ring R (add-ℕ n m) x y) ∙
              (split-sum-Commutative-Ring R n _ _) ∙ 
              {!   !})))
```

### The nilradical is closed under multiplication with ring elements

```agda
is-closed-under-multiplication-subset-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) {x y : type-Commutative-Ring R} →
  is-in-subtype (subset-nilradical-Commutative-Ring R) x → 
  is-in-subtype
    ( subset-nilradical-Commutative-Ring R)
    ( mul-Commutative-Ring R x y)
is-closed-under-multiplication-subset-nilradical-Commutative-Ring R {x} {y} f = 
  apply-universal-property-trunc-Prop f 
    ( subset-nilradical-Commutative-Ring R (mul-Commutative-Ring R x y)) 
    ( λ (n , p) →
      intro-∃ n
        ( ( distributive-power-mul-Commutative-Ring R n) ∙ 
          ( ( ap (mul-Commutative-Ring' R (power-Commutative-Ring R n y)) p) ∙ 
            ( left-zero-law-mul-Commutative-Ring R
              ( power-Commutative-Ring R n y)))))
```
