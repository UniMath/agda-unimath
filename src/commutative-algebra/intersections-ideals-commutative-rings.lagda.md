# Intersections of ideals of commutative rings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module commutative-algebra.intersections-ideals-commutative-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings funext univalence truncations
open import commutative-algebra.ideals-commutative-rings funext univalence truncations
open import commutative-algebra.poset-of-ideals-commutative-rings funext univalence truncations
open import commutative-algebra.subsets-commutative-rings funext univalence truncations

open import foundation.dependent-pair-types
open import foundation.intersections-subtypes funext univalence truncations
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets funext univalence truncations

open import ring-theory.intersections-ideals-rings funext univalence truncations
```

</details>

## Idea

The **intersection** of two ideals `I` and `J` in a commutative ring is the
ideal consisting of the elements contained in both of the ideals `I` and `J`.

## Definitions

### The universal property of intersections of radical ideals

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 A)
  (J : ideal-Commutative-Ring l3 A)
  where

  is-intersection-ideal-Commutative-Ring :
    {l4 : Level} (K : ideal-Commutative-Ring l4 A) → UUω
  is-intersection-ideal-Commutative-Ring K =
    is-greatest-binary-lower-bound-Large-Poset
      ( ideal-Commutative-Ring-Large-Poset A)
      ( I)
      ( J)
      ( K)
```

### Intersections of ideals in commutative rings

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 R) (J : ideal-Commutative-Ring l3 R)
  where

  subset-intersection-ideal-Commutative-Ring :
    subset-Commutative-Ring (l2 ⊔ l3) R
  subset-intersection-ideal-Commutative-Ring =
    intersection-subtype
      ( subset-ideal-Commutative-Ring R I)
      ( subset-ideal-Commutative-Ring R J)

  is-in-intersection-ideal-Commutative-Ring :
    type-Commutative-Ring R → UU (l2 ⊔ l3)
  is-in-intersection-ideal-Commutative-Ring =
    is-in-subtype subset-intersection-ideal-Commutative-Ring

  contains-zero-intersection-ideal-Commutative-Ring :
    is-in-intersection-ideal-Commutative-Ring (zero-Commutative-Ring R)
  pr1 contains-zero-intersection-ideal-Commutative-Ring =
    contains-zero-ideal-Commutative-Ring R I
  pr2 contains-zero-intersection-ideal-Commutative-Ring =
    contains-zero-ideal-Commutative-Ring R J

  is-closed-under-addition-intersection-ideal-Commutative-Ring :
    is-closed-under-addition-subset-Commutative-Ring R
      ( subset-intersection-ideal-Commutative-Ring)
  pr1
    ( is-closed-under-addition-intersection-ideal-Commutative-Ring
      ( H1 , H2)
      ( K1 , K2)) =
    is-closed-under-addition-ideal-Commutative-Ring R I H1 K1
  pr2
    ( is-closed-under-addition-intersection-ideal-Commutative-Ring
      ( H1 , H2)
      ( K1 , K2)) =
    is-closed-under-addition-ideal-Commutative-Ring R J H2 K2

  is-closed-under-negatives-intersection-ideal-Commutative-Ring :
    is-closed-under-negatives-subset-Commutative-Ring R
      ( subset-intersection-ideal-Commutative-Ring)
  pr1
    ( is-closed-under-negatives-intersection-ideal-Commutative-Ring
      ( H1 , H2)) =
    is-closed-under-negatives-ideal-Commutative-Ring R I H1
  pr2
    ( is-closed-under-negatives-intersection-ideal-Commutative-Ring
      ( H1 , H2)) =
    is-closed-under-negatives-ideal-Commutative-Ring R J H2

  is-additive-subgroup-intersection-ideal-Commutative-Ring :
    is-additive-subgroup-subset-Commutative-Ring R
      ( subset-intersection-ideal-Commutative-Ring)
  pr1 is-additive-subgroup-intersection-ideal-Commutative-Ring =
    contains-zero-intersection-ideal-Commutative-Ring
  pr1 (pr2 is-additive-subgroup-intersection-ideal-Commutative-Ring) =
    is-closed-under-addition-intersection-ideal-Commutative-Ring
  pr2 (pr2 is-additive-subgroup-intersection-ideal-Commutative-Ring) =
    is-closed-under-negatives-intersection-ideal-Commutative-Ring

  is-closed-under-left-multiplication-intersection-ideal-Commutative-Ring :
    is-closed-under-left-multiplication-subset-Commutative-Ring R
      ( subset-intersection-ideal-Commutative-Ring)
  pr1
    ( is-closed-under-left-multiplication-intersection-ideal-Commutative-Ring
      x y (H1 , H2)) =
    is-closed-under-left-multiplication-ideal-Commutative-Ring R I x y H1
  pr2
    ( is-closed-under-left-multiplication-intersection-ideal-Commutative-Ring
      x y (H1 , H2)) =
    is-closed-under-left-multiplication-ideal-Commutative-Ring R J x y H2

  intersection-ideal-Commutative-Ring : ideal-Commutative-Ring (l2 ⊔ l3) R
  intersection-ideal-Commutative-Ring =
    ideal-left-ideal-Commutative-Ring R
      subset-intersection-ideal-Commutative-Ring
      contains-zero-intersection-ideal-Commutative-Ring
      is-closed-under-addition-intersection-ideal-Commutative-Ring
      is-closed-under-negatives-intersection-ideal-Commutative-Ring
      is-closed-under-left-multiplication-intersection-ideal-Commutative-Ring

  is-intersection-intersection-ideal-Commutative-Ring :
    is-intersection-ideal-Commutative-Ring R I J
      ( intersection-ideal-Commutative-Ring)
  is-intersection-intersection-ideal-Commutative-Ring =
    is-intersection-intersection-ideal-Ring (ring-Commutative-Ring R) I J
```
