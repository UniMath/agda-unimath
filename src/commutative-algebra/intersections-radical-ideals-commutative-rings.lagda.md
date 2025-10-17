# Intersections of radical ideals of commutative rings

```agda
module commutative-algebra.intersections-radical-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.full-ideals-commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.intersections-ideals-commutative-rings
open import commutative-algebra.poset-of-ideals-commutative-rings
open import commutative-algebra.poset-of-radical-ideals-commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.products-ideals-commutative-rings
open import commutative-algebra.products-radical-ideals-commutative-rings
open import commutative-algebra.radical-ideals-commutative-rings
open import commutative-algebra.radicals-of-ideals-commutative-rings

open import elementary-number-theory.addition-natural-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.functoriality-propositional-truncations
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-meet-semilattices
```

</details>

## Idea

The **intersection** of two
[radical ideals](commutative-algebra.radical-ideals-commutative-rings.md)
consists of the elements contained in both of them. Given two radical ideals `I`
and `J`, their intersection can be computed as

```text
  I ∩ J ＝ √ IJ,
```

where `IJ` is the
[product](commutative-algebra.products-ideals-commutative-rings.md) of `I` and
`J`.

## Definition

### The universal property of intersections of radical ideals

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : radical-ideal-Commutative-Ring l2 A)
  (J : radical-ideal-Commutative-Ring l3 A)
  where

  is-intersection-radical-ideal-Commutative-Ring :
    {l4 : Level} (K : radical-ideal-Commutative-Ring l4 A) → UUω
  is-intersection-radical-ideal-Commutative-Ring K =
    is-greatest-binary-lower-bound-Large-Poset
      ( radical-ideal-Commutative-Ring-Large-Poset A)
      ( I)
      ( J)
      ( K)
```

### The intersection of radical ideals

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : radical-ideal-Commutative-Ring l2 A)
  (J : radical-ideal-Commutative-Ring l3 A)
  where

  is-radical-intersection-radical-ideal-Commutative-Ring :
    is-radical-ideal-Commutative-Ring A
      ( intersection-ideal-Commutative-Ring A
        ( ideal-radical-ideal-Commutative-Ring A I)
        ( ideal-radical-ideal-Commutative-Ring A J))
  pr1 (is-radical-intersection-radical-ideal-Commutative-Ring x n (H , K)) =
    is-radical-radical-ideal-Commutative-Ring A I x n H
  pr2 (is-radical-intersection-radical-ideal-Commutative-Ring x n (H , K)) =
    is-radical-radical-ideal-Commutative-Ring A J x n K

  intersection-radical-ideal-Commutative-Ring :
    radical-ideal-Commutative-Ring (l2 ⊔ l3) A
  pr1 intersection-radical-ideal-Commutative-Ring =
    intersection-ideal-Commutative-Ring A
      ( ideal-radical-ideal-Commutative-Ring A I)
      ( ideal-radical-ideal-Commutative-Ring A J)
  pr2 intersection-radical-ideal-Commutative-Ring =
    is-radical-intersection-radical-ideal-Commutative-Ring

  ideal-intersection-radical-ideal-Commutative-Ring :
    ideal-Commutative-Ring (l2 ⊔ l3) A
  ideal-intersection-radical-ideal-Commutative-Ring =
    ideal-radical-ideal-Commutative-Ring A
      intersection-radical-ideal-Commutative-Ring

  is-intersection-intersection-radical-ideal-Commutative-Ring :
    is-intersection-radical-ideal-Commutative-Ring A I J
      intersection-radical-ideal-Commutative-Ring
  is-intersection-intersection-radical-ideal-Commutative-Ring K =
    is-intersection-intersection-ideal-Commutative-Ring A
      ( ideal-radical-ideal-Commutative-Ring A I)
      ( ideal-radical-ideal-Commutative-Ring A J)
      ( ideal-radical-ideal-Commutative-Ring A K)
```

### The large meet-semilattice of radical ideals in a commutative ring

```agda
module _
  {l1 : Level} (A : Commutative-Ring l1)
  where

  has-meets-radical-ideal-Commutative-Ring :
    has-meets-Large-Poset (radical-ideal-Commutative-Ring-Large-Poset A)
  meet-has-meets-Large-Poset
    has-meets-radical-ideal-Commutative-Ring =
    intersection-radical-ideal-Commutative-Ring A
  is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
    has-meets-radical-ideal-Commutative-Ring =
    is-intersection-intersection-radical-ideal-Commutative-Ring A

  is-large-meet-semilattice-radical-ideal-Commutative-Ring :
    is-large-meet-semilattice-Large-Poset
      ( radical-ideal-Commutative-Ring-Large-Poset A)
  has-meets-is-large-meet-semilattice-Large-Poset
    is-large-meet-semilattice-radical-ideal-Commutative-Ring =
    has-meets-radical-ideal-Commutative-Ring
  has-top-element-is-large-meet-semilattice-Large-Poset
    is-large-meet-semilattice-radical-ideal-Commutative-Ring =
    has-top-element-radical-ideal-Commutative-Ring A

  radical-ideal-Commutative-Ring-Large-Meet-Semilattice :
    Large-Meet-Semilattice (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-poset-Large-Meet-Semilattice
    radical-ideal-Commutative-Ring-Large-Meet-Semilattice =
    radical-ideal-Commutative-Ring-Large-Poset A
  is-large-meet-semilattice-Large-Meet-Semilattice
    radical-ideal-Commutative-Ring-Large-Meet-Semilattice =
    is-large-meet-semilattice-radical-ideal-Commutative-Ring
```

## Properties

### The radical ideal of an intersection is the intersection of the radicals of the ideals

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 A) (J : ideal-Commutative-Ring l3 A)
  where

  forward-inclusion-intersection-radical-of-ideal-Commutative-Ring :
    leq-ideal-Commutative-Ring A
      ( intersection-ideal-Commutative-Ring A
        ( ideal-radical-of-ideal-Commutative-Ring A I)
        ( ideal-radical-of-ideal-Commutative-Ring A J))
      ( ideal-radical-of-ideal-Commutative-Ring A
        ( intersection-ideal-Commutative-Ring A I J))
  forward-inclusion-intersection-radical-of-ideal-Commutative-Ring x (H , K) =
    map-binary-trunc-Prop
      ( λ (n , H') (m , K') →
        ( add-ℕ n m) ,
        ( ( is-closed-under-eq-ideal-Commutative-Ring A I
            ( is-closed-under-right-multiplication-ideal-Commutative-Ring
              ( A)
              ( I)
              ( power-Commutative-Ring A n x)
              ( power-Commutative-Ring A m x)
              ( H'))
            ( inv ( distributive-power-add-Commutative-Ring A n m))) ,
          ( is-closed-under-eq-ideal-Commutative-Ring A J
            ( is-closed-under-left-multiplication-ideal-Commutative-Ring
              ( A)
              ( J)
              ( power-Commutative-Ring A n x)
              ( power-Commutative-Ring A m x)
              ( K'))
            ( inv ( distributive-power-add-Commutative-Ring A n m)))))
      ( H)
      ( K)

  backward-inclusion-intersection-radical-of-ideal-Commutative-Ring :
    leq-ideal-Commutative-Ring A
      ( ideal-radical-of-ideal-Commutative-Ring A
        ( intersection-ideal-Commutative-Ring A I J))
      ( intersection-ideal-Commutative-Ring A
        ( ideal-radical-of-ideal-Commutative-Ring A I)
        ( ideal-radical-of-ideal-Commutative-Ring A J))
  backward-inclusion-intersection-radical-of-ideal-Commutative-Ring x H =
    apply-universal-property-trunc-Prop H
      ( subset-intersection-ideal-Commutative-Ring A
        ( ideal-radical-of-ideal-Commutative-Ring A I)
        ( ideal-radical-of-ideal-Commutative-Ring A J)
        ( x))
      ( λ (n , H' , K') →
        ( intro-exists n H' , intro-exists n K'))

  preserves-intersection-radical-of-ideal-Commutative-Ring :
    ( intersection-ideal-Commutative-Ring A
      ( ideal-radical-of-ideal-Commutative-Ring A I)
      ( ideal-radical-of-ideal-Commutative-Ring A J)) ＝
    ( ideal-radical-of-ideal-Commutative-Ring A
      ( intersection-ideal-Commutative-Ring A I J))
  preserves-intersection-radical-of-ideal-Commutative-Ring =
    eq-has-same-elements-ideal-Commutative-Ring A
      ( intersection-ideal-Commutative-Ring A
        ( ideal-radical-of-ideal-Commutative-Ring A I)
        ( ideal-radical-of-ideal-Commutative-Ring A J))
      ( ideal-radical-of-ideal-Commutative-Ring A
        ( intersection-ideal-Commutative-Ring A I J))
      ( λ x →
        forward-inclusion-intersection-radical-of-ideal-Commutative-Ring x ,
        backward-inclusion-intersection-radical-of-ideal-Commutative-Ring x)
```

### The intersection of radical ideals is the radical of the ideal generated by their product

Given two radical ideals `I` and `J`, we claim that

```text
  I ∩ J ＝ √ IJ,
```

where `IJ` is the
[product](commutative-algebra.products-ideals-commutative-rings.md) of the
ideals `I` and `J`. To prove this, it suffices to prove the inclusions

```text
  IJ ⊆ I ∩ J ⊆ √ IJ.
```

Note that any product of elements in `I` and `J` is in the intersection `I ∩ J`.
This settles the first inclusion. For the second inclusion, note that if
`x ∈ I ∩ J`, then `x² ∈ IJ` so it follows that `x ∈ √ IJ`.

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : radical-ideal-Commutative-Ring l2 A)
  (J : radical-ideal-Commutative-Ring l3 A)
  where

  contains-product-intersection-radical-ideal-Commutative-Ring :
    contains-product-radical-ideal-Commutative-Ring A I J
      ( intersection-radical-ideal-Commutative-Ring A I J)
  pr1 (contains-product-intersection-radical-ideal-Commutative-Ring x y p q) =
    is-closed-under-right-multiplication-radical-ideal-Commutative-Ring
      A I x y p
  pr2 (contains-product-intersection-radical-ideal-Commutative-Ring x y p q) =
    is-closed-under-left-multiplication-radical-ideal-Commutative-Ring
      A J x y q

  forward-inclusion-intersection-radical-ideal-Commutative-Ring :
    leq-radical-ideal-Commutative-Ring A
      ( intersection-radical-ideal-Commutative-Ring A I J)
      ( product-radical-ideal-Commutative-Ring A I J)
  forward-inclusion-intersection-radical-ideal-Commutative-Ring x (H , K) =
    is-radical-radical-of-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A
        ( ideal-radical-ideal-Commutative-Ring A I)
        ( ideal-radical-ideal-Commutative-Ring A J))
      ( x)
      ( 2)
      ( contains-product-product-radical-ideal-Commutative-Ring A I J x x H K)

  backward-inclusion-intersection-radical-ideal-Commutative-Ring :
    leq-radical-ideal-Commutative-Ring A
      ( product-radical-ideal-Commutative-Ring A I J)
      ( intersection-radical-ideal-Commutative-Ring A I J)
  backward-inclusion-intersection-radical-ideal-Commutative-Ring =
    is-radical-of-ideal-radical-of-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A
        ( ideal-radical-ideal-Commutative-Ring A I)
        ( ideal-radical-ideal-Commutative-Ring A J))
      ( intersection-radical-ideal-Commutative-Ring A I J)
      ( is-product-product-ideal-Commutative-Ring A
        ( ideal-radical-ideal-Commutative-Ring A I)
        ( ideal-radical-ideal-Commutative-Ring A J)
        ( ideal-intersection-radical-ideal-Commutative-Ring A I J)
        ( contains-product-intersection-radical-ideal-Commutative-Ring))

  has-same-elements-intersection-radical-ideal-Commutative-Ring :
    has-same-elements-radical-ideal-Commutative-Ring A
      ( intersection-radical-ideal-Commutative-Ring A I J)
      ( product-radical-ideal-Commutative-Ring A I J)
  pr1 (has-same-elements-intersection-radical-ideal-Commutative-Ring x) =
    forward-inclusion-intersection-radical-ideal-Commutative-Ring x
  pr2 (has-same-elements-intersection-radical-ideal-Commutative-Ring x) =
    backward-inclusion-intersection-radical-ideal-Commutative-Ring x

  is-product-intersection-radical-ideal-Commutative-Ring :
    is-product-radical-ideal-Commutative-Ring A I J
      ( intersection-radical-ideal-Commutative-Ring A I J)
      ( contains-product-intersection-radical-ideal-Commutative-Ring)
  is-product-intersection-radical-ideal-Commutative-Ring K H x p =
    is-product-product-radical-ideal-Commutative-Ring A I J K H x
      ( forward-inclusion-intersection-radical-ideal-Commutative-Ring x p)

  is-intersection-product-radical-ideal-Commutative-Ring :
    is-intersection-radical-ideal-Commutative-Ring A I J
      ( product-radical-ideal-Commutative-Ring A I J)
  pr1 (is-intersection-product-radical-ideal-Commutative-Ring K) (L , M) x p =
    forward-inclusion-intersection-radical-ideal-Commutative-Ring x
      ( L x p , M x p)
  pr1 (pr2 (is-intersection-product-radical-ideal-Commutative-Ring K) H) x p =
    pr1
      ( backward-inclusion-intersection-radical-ideal-Commutative-Ring x
        ( H x p))
  pr2 (pr2 (is-intersection-product-radical-ideal-Commutative-Ring K) H) x p =
    pr2
      ( backward-inclusion-intersection-radical-ideal-Commutative-Ring x
        ( H x p))
```
