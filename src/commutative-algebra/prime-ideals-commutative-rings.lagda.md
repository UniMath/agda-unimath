# Prime ideals in commutative rings

```agda
module commutative-algebra.prime-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings

open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.ideals-rings
```

</details>

## Idea

A prime ideal is an ideal `I` in a commutative ring `R` such that for every `a,b : R` whe have `ab ∈ I ⇒ (a ∈ I) ∨ (b ∈ I)`.

## Definition

```agda
module _
  {l1 l2 : Level} (R : Commutative-Ring l1) (I : ideal-Commutative-Ring l2 R)
  where

  is-prime-ideal-commutative-ring-Prop : Prop (l1 ⊔ l2)
  is-prime-ideal-commutative-ring-Prop =
    Π-Prop
      ( type-Commutative-Ring R)
      ( λ a →
        Π-Prop
          ( type-Commutative-Ring R)
          ( λ b →
            function-Prop
              ( is-in-ideal-Commutative-Ring R I (mul-Commutative-Ring R a b))
              ( disj-Prop
                ( subset-ideal-Commutative-Ring R I a)
                ( subset-ideal-Commutative-Ring R I b))))

  is-prime-ideal-Commutative-Ring : UU (l1 ⊔ l2)
  is-prime-ideal-Commutative-Ring =
    type-Prop is-prime-ideal-commutative-ring-Prop

  is-prop-is-prime-ideal-Commutative-Ring :
    is-prop is-prime-ideal-Commutative-Ring
  is-prop-is-prime-ideal-Commutative-Ring =
    is-prop-type-Prop is-prime-ideal-commutative-ring-Prop

prime-ideal-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
prime-ideal-Commutative-Ring l2 R =
  Σ (ideal-Commutative-Ring l2 R) (is-prime-ideal-Commutative-Ring R)

module _
  {l1 l2 : Level} (R : Commutative-Ring l1)
  (P : prime-ideal-Commutative-Ring l2 R)
  where

  ideal-prime-ideal-Commutative-Ring : ideal-Commutative-Ring l2 R
  ideal-prime-ideal-Commutative-Ring = pr1 P

  is-prime-ideal-ideal-prime-ideal-Commutative-Ring :
    is-prime-ideal-Commutative-Ring R ideal-prime-ideal-Commutative-Ring
  is-prime-ideal-ideal-prime-ideal-Commutative-Ring = pr2 P

  subset-prime-ideal-Commutative-Ring : subset-Commutative-Ring l2 R
  subset-prime-ideal-Commutative-Ring =
    subset-ideal-Commutative-Ring R ideal-prime-ideal-Commutative-Ring

  is-in-prime-ideal-Commutative-Ring : type-Commutative-Ring R → UU l2
  is-in-prime-ideal-Commutative-Ring =
    is-in-ideal-Commutative-Ring R ideal-prime-ideal-Commutative-Ring

  type-prime-ideal-Commutative-Ring : UU (l1 ⊔ l2)
  type-prime-ideal-Commutative-Ring =
    type-ideal-Commutative-Ring R ideal-prime-ideal-Commutative-Ring

  inclusion-prime-ideal-Commutative-Ring :
    type-prime-ideal-Commutative-Ring → type-Commutative-Ring R
  inclusion-prime-ideal-Commutative-Ring =
    inclusion-subset-Commutative-Ring R subset-prime-ideal-Commutative-Ring

  is-ideal-subset-prime-ideal-Commutative-Ring :
    is-ideal-subset-Commutative-Ring R subset-prime-ideal-Commutative-Ring
  is-ideal-subset-prime-ideal-Commutative-Ring =
    is-ideal-subset-ideal-Commutative-Ring R ideal-prime-ideal-Commutative-Ring

  is-additive-subgroup-subset-prime-ideal-Commutative-Ring :
    is-additive-subgroup-subset-Ring
      ( ring-Commutative-Ring R)
      ( subset-prime-ideal-Commutative-Ring)
  is-additive-subgroup-subset-prime-ideal-Commutative-Ring =
    is-additive-subgroup-subset-ideal-Commutative-Ring R
      ideal-prime-ideal-Commutative-Ring

  contains-zero-prime-ideal-Commutative-Ring :
    is-in-prime-ideal-Commutative-Ring (zero-Commutative-Ring R)
  contains-zero-prime-ideal-Commutative-Ring =
    contains-zero-ideal-Commutative-Ring R ideal-prime-ideal-Commutative-Ring

  is-closed-under-add-prime-ideal-Commutative-Ring :
    {x y : type-Commutative-Ring R} →
    is-in-prime-ideal-Commutative-Ring x →
    is-in-prime-ideal-Commutative-Ring y →
    is-in-prime-ideal-Commutative-Ring (add-Commutative-Ring R x y)
  is-closed-under-add-prime-ideal-Commutative-Ring =
    is-closed-under-add-ideal-Commutative-Ring R
      ideal-prime-ideal-Commutative-Ring

  is-closed-under-mul-left-prime-ideal-Commutative-Ring :
    is-closed-under-mul-left-subset-Commutative-Ring R
      subset-prime-ideal-Commutative-Ring
  is-closed-under-mul-left-prime-ideal-Commutative-Ring =
    is-closed-under-mul-left-ideal-Commutative-Ring R
      ideal-prime-ideal-Commutative-Ring

  is-closed-under-mul-right-prime-ideal-Commutative-Ring :
    is-closed-under-mul-right-subset-Commutative-Ring R
      subset-prime-ideal-Commutative-Ring
  is-closed-under-mul-right-prime-ideal-Commutative-Ring =
    is-closed-under-mul-right-ideal-Commutative-Ring R
      ideal-prime-ideal-Commutative-Ring
```
