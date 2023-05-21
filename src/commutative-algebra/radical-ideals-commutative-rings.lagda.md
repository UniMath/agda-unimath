# Radical ideals in commutative rings

```agda
module commutative-algebra.radical-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

An ideal `I` in a commutative ring is said to be **radical** if for every
element `f : A` such that there exists an `n` such that `fⁿ ∈ I`, we have
`f ∈ I`. In other words, radical ideals are ideals that contain, for every
element `u ∈ I`, also the `n`-th roots of `u` if it has any.

## Definition

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1)

  where

  is-radical-ideal-commutative-ring-Prop :
    (I : ideal-Commutative-Ring l2 A) → Prop (l1 ⊔ l2)
  is-radical-ideal-commutative-ring-Prop I =
    Π-Prop
      ( type-Commutative-Ring A)
      ( λ f →
        Π-Prop ℕ
          ( λ n →
            function-Prop
              ( is-in-ideal-Commutative-Ring A I (power-Commutative-Ring A n f))
              ( subset-ideal-Commutative-Ring A I f)))

  is-radical-ideal-Commutative-Ring :
    (I : ideal-Commutative-Ring l2 A) → UU (l1 ⊔ l2)
  is-radical-ideal-Commutative-Ring I =
    type-Prop (is-radical-ideal-commutative-ring-Prop I)

  is-prop-is-radical-ideal-Commutative-Ring :
    (I : ideal-Commutative-Ring l2 A) →
    is-prop (is-radical-ideal-Commutative-Ring I)
  is-prop-is-radical-ideal-Commutative-Ring I =
    is-prop-type-Prop (is-radical-ideal-commutative-ring-Prop I)

radical-ideal-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
radical-ideal-Commutative-Ring l2 A =
  Σ (ideal-Commutative-Ring l2 A) (is-radical-ideal-Commutative-Ring A)

module _
  {l1 l2 : Level} (A : Commutative-Ring l1)
  (I : radical-ideal-Commutative-Ring l2 A)
  where

  ideal-radical-ideal-Commutative-Ring : ideal-Commutative-Ring l2 A
  ideal-radical-ideal-Commutative-Ring = pr1 I

  is-radical-radical-ideal-Commutative-Ring :
    is-radical-ideal-Commutative-Ring A ideal-radical-ideal-Commutative-Ring
  is-radical-radical-ideal-Commutative-Ring = pr2 I

  subset-radical-ideal-Commutative-Ring : subset-Commutative-Ring l2 A
  subset-radical-ideal-Commutative-Ring =
    subset-ideal-Commutative-Ring A ideal-radical-ideal-Commutative-Ring

  is-in-radical-ideal-Commutative-Ring : type-Commutative-Ring A → UU l2
  is-in-radical-ideal-Commutative-Ring =
    is-in-ideal-Commutative-Ring A ideal-radical-ideal-Commutative-Ring

  is-closed-under-eq-radical-ideal-Commutative-Ring :
    {x y : type-Commutative-Ring A} → is-in-radical-ideal-Commutative-Ring x →
    (x ＝ y) → is-in-radical-ideal-Commutative-Ring y
  is-closed-under-eq-radical-ideal-Commutative-Ring =
    is-closed-under-eq-subset-Commutative-Ring A
      subset-radical-ideal-Commutative-Ring

  is-closed-under-eq-radical-ideal-Commutative-Ring' :
    {x y : type-Commutative-Ring A} → is-in-radical-ideal-Commutative-Ring y →
    (x ＝ y) → is-in-radical-ideal-Commutative-Ring x
  is-closed-under-eq-radical-ideal-Commutative-Ring' =
    is-closed-under-eq-subset-Commutative-Ring' A
      subset-radical-ideal-Commutative-Ring

  type-radical-ideal-Commutative-Ring : UU (l1 ⊔ l2)
  type-radical-ideal-Commutative-Ring =
    type-ideal-Commutative-Ring A ideal-radical-ideal-Commutative-Ring

  inclusion-radical-ideal-Commutative-Ring :
    type-radical-ideal-Commutative-Ring → type-Commutative-Ring A
  inclusion-radical-ideal-Commutative-Ring =
    inclusion-ideal-Commutative-Ring A ideal-radical-ideal-Commutative-Ring

  is-ideal-radical-ideal-Commutative-Ring :
    is-ideal-subset-Commutative-Ring A subset-radical-ideal-Commutative-Ring
  is-ideal-radical-ideal-Commutative-Ring =
    is-ideal-ideal-Commutative-Ring A
      ideal-radical-ideal-Commutative-Ring

  contains-zero-radical-ideal-Commutative-Ring :
    is-in-radical-ideal-Commutative-Ring (zero-Commutative-Ring A)
  contains-zero-radical-ideal-Commutative-Ring =
    contains-zero-ideal-Commutative-Ring A ideal-radical-ideal-Commutative-Ring

  is-closed-under-addition-radical-ideal-Commutative-Ring :
    is-closed-under-addition-subset-Commutative-Ring A
      subset-radical-ideal-Commutative-Ring
  is-closed-under-addition-radical-ideal-Commutative-Ring =
    is-closed-under-addition-ideal-Commutative-Ring A
      ideal-radical-ideal-Commutative-Ring

  is-closed-under-left-multiplication-radical-ideal-Commutative-Ring :
    is-closed-under-left-multiplication-subset-Commutative-Ring A
      subset-radical-ideal-Commutative-Ring
  is-closed-under-left-multiplication-radical-ideal-Commutative-Ring =
    is-closed-under-left-multiplication-ideal-Commutative-Ring A
      ideal-radical-ideal-Commutative-Ring

  is-closed-under-right-multiplication-radical-ideal-Commutative-Ring :
    is-closed-under-right-multiplication-subset-Commutative-Ring A
      subset-radical-ideal-Commutative-Ring
  is-closed-under-right-multiplication-radical-ideal-Commutative-Ring =
    is-closed-under-right-multiplication-ideal-Commutative-Ring A
      ideal-radical-ideal-Commutative-Ring
```

### Intersection of radical ideals is radical

```agda
  is-radical-intersection-radical-ideal-Commutative-Ring :
    {l1 l2 l3 : Level} ( R : Commutative-Ring l1)
    (I : radical-ideal-Commutative-Ring l2 R)
    (J : radical-ideal-Commutative-Ring l3 R) →
    is-radical-ideal-Commutative-Ring R
      ( intersection-ideal-Commutative-Ring R (pr1 I) (pr1 J))
  pr1
    ( is-radical-intersection-radical-ideal-Commutative-Ring
      R (I , K) J x n H) =
    K x n (pr1 H)
  pr2
    ( is-radical-intersection-radical-ideal-Commutative-Ring
      R I (J , K) x n H) =
    K x n (pr2 H)
```
