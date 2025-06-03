# Products of ideals of commutative rings

```agda
module commutative-algebra.products-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.ideals-generated-by-subsets-commutative-rings
open import commutative-algebra.poset-of-ideals-commutative-rings
open import commutative-algebra.products-subsets-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import lists.lists

open import ring-theory.products-ideals-rings
```

</details>

## Idea

The **product** of two [ideals](commutative-algebra.ideals-commutative-rings.md)
`I` and `J` in a [commutative ring](commutative-algebra.commutative-rings.md) is
the ideal generated all products of elements in `I` and `J`.

## Definition

### The universal property of the product of two ideals in a commutative ring

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 R) (J : ideal-Commutative-Ring l3 R)
  where

  contains-product-ideal-Commutative-Ring :
    {l4 : Level} (K : ideal-Commutative-Ring l4 R) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  contains-product-ideal-Commutative-Ring =
    contains-product-ideal-Ring (ring-Commutative-Ring R) I J

  is-product-ideal-Commutative-Ring :
    {l4 : Level} (K : ideal-Commutative-Ring l4 R) →
    contains-product-ideal-Commutative-Ring K → UUω
  is-product-ideal-Commutative-Ring =
    is-product-ideal-Ring (ring-Commutative-Ring R) I J
```

### The product of two ideals in a commutative ring

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 A) (J : ideal-Commutative-Ring l3 A)
  where

  generating-subset-product-ideal-Commutative-Ring :
    subset-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  generating-subset-product-ideal-Commutative-Ring =
    generating-subset-product-ideal-Ring (ring-Commutative-Ring A) I J

  product-ideal-Commutative-Ring : ideal-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  product-ideal-Commutative-Ring =
    product-ideal-Ring (ring-Commutative-Ring A) I J

  subset-product-ideal-Commutative-Ring :
    subset-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  subset-product-ideal-Commutative-Ring =
    subset-ideal-Commutative-Ring A product-ideal-Commutative-Ring

  is-in-product-ideal-Commutative-Ring :
    type-Commutative-Ring A → UU (l1 ⊔ l2 ⊔ l3)
  is-in-product-ideal-Commutative-Ring =
    is-in-ideal-Commutative-Ring A product-ideal-Commutative-Ring

  is-closed-under-eq-product-ideal-Commutative-Ring :
    {x y : type-Commutative-Ring A} → is-in-product-ideal-Commutative-Ring x →
    (x ＝ y) → is-in-product-ideal-Commutative-Ring y
  is-closed-under-eq-product-ideal-Commutative-Ring =
    is-closed-under-eq-ideal-Commutative-Ring A product-ideal-Commutative-Ring

  is-closed-under-eq-product-ideal-Commutative-Ring' :
    {x y : type-Commutative-Ring A} → is-in-product-ideal-Commutative-Ring y →
    (x ＝ y) → is-in-product-ideal-Commutative-Ring x
  is-closed-under-eq-product-ideal-Commutative-Ring' =
    is-closed-under-eq-ideal-Commutative-Ring' A product-ideal-Commutative-Ring

  contains-product-product-ideal-Commutative-Ring :
    contains-product-ideal-Commutative-Ring A I J product-ideal-Commutative-Ring
  contains-product-product-ideal-Commutative-Ring =
    contains-product-product-ideal-Ring (ring-Commutative-Ring A) I J

  is-product-product-ideal-Commutative-Ring :
    is-product-ideal-Commutative-Ring A I J
      product-ideal-Commutative-Ring
      contains-product-product-ideal-Commutative-Ring
  is-product-product-ideal-Commutative-Ring =
    is-product-product-ideal-Ring (ring-Commutative-Ring A) I J
```

## Properties

### The product of ideals preserves inequality of ideals

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (A : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 A)
  (J : ideal-Commutative-Ring l3 A)
  (K : ideal-Commutative-Ring l4 A)
  (L : ideal-Commutative-Ring l5 A)
  where

  preserves-order-product-ideal-Commutative-Ring :
    leq-ideal-Commutative-Ring A I J →
    leq-ideal-Commutative-Ring A K L →
    leq-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A I K)
      ( product-ideal-Commutative-Ring A J L)
  preserves-order-product-ideal-Commutative-Ring p q =
    is-product-product-ideal-Commutative-Ring A I K
      ( product-ideal-Commutative-Ring A J L)
      ( λ x y u v →
        contains-product-product-ideal-Commutative-Ring A J L _ _
          ( p x u)
          ( q y v))

module _
  {l1 l2 l3 l4 : Level} (A : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 A)
  (J : ideal-Commutative-Ring l3 A)
  (K : ideal-Commutative-Ring l4 A)
  where

  preserves-order-left-product-ideal-Commutative-Ring :
    leq-ideal-Commutative-Ring A I J →
    leq-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A I K)
      ( product-ideal-Commutative-Ring A J K)
  preserves-order-left-product-ideal-Commutative-Ring p =
    preserves-order-product-ideal-Commutative-Ring A I J K K p
      ( refl-leq-ideal-Commutative-Ring A K)

  preserves-order-right-product-ideal-Commutative-Ring :
    leq-ideal-Commutative-Ring A J K →
    leq-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A I J)
      ( product-ideal-Commutative-Ring A I K)
  preserves-order-right-product-ideal-Commutative-Ring =
    preserves-order-product-ideal-Commutative-Ring A I I J K
      ( refl-leq-ideal-Commutative-Ring A I)
```

### The ideal generated by a product of two subsets is the product of the ideals generated by the two subsets

In other words, we will show that `(S)(T) = (ST)`.

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (S : subset-Commutative-Ring l2 A) (T : subset-Commutative-Ring l3 A)
  where

  abstract
    forward-inclusion-preserves-product-ideal-subset-Commutative-Ring :
      leq-ideal-Commutative-Ring A
        ( ideal-subset-Commutative-Ring A
          ( product-subset-Commutative-Ring A S T))
        ( product-ideal-Commutative-Ring A
          ( ideal-subset-Commutative-Ring A S)
          ( ideal-subset-Commutative-Ring A T))
    forward-inclusion-preserves-product-ideal-subset-Commutative-Ring =
      is-ideal-generated-by-subset-ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A S T)
        ( product-ideal-Commutative-Ring A
          ( ideal-subset-Commutative-Ring A S)
          ( ideal-subset-Commutative-Ring A T))
        ( λ x H →
          apply-universal-property-trunc-Prop H
            ( subset-product-ideal-Commutative-Ring A
              ( ideal-subset-Commutative-Ring A S)
              ( ideal-subset-Commutative-Ring A T)
              ( x))
            ( λ where
              ( s , t , refl) →
                contains-product-product-ideal-Commutative-Ring A
                  ( ideal-subset-Commutative-Ring A S)
                  ( ideal-subset-Commutative-Ring A T)
                  ( pr1 s)
                  ( pr1 t)
                  ( contains-subset-ideal-subset-Commutative-Ring A S
                    ( pr1 s)
                    ( pr2 s))
                  ( contains-subset-ideal-subset-Commutative-Ring A T
                    ( pr1 t)
                    ( pr2 t))))

  left-backward-inclusion-preserves-product-ideal-subset-Commutative-Ring :
    {x s y : type-Commutative-Ring A} →
    is-in-subset-Commutative-Ring A S s →
    (l : formal-combination-subset-Commutative-Ring A T) →
    is-in-ideal-subset-Commutative-Ring A
      ( product-subset-Commutative-Ring A S T)
      ( mul-Commutative-Ring A
        ( mul-Commutative-Ring A (mul-Commutative-Ring A x s) y)
        ( ev-formal-combination-subset-Commutative-Ring A T l))
  left-backward-inclusion-preserves-product-ideal-subset-Commutative-Ring
    H nil =
    is-closed-under-eq-ideal-subset-Commutative-Ring' A
      ( product-subset-Commutative-Ring A S T)
      ( contains-zero-ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A S T))
      ( right-zero-law-mul-Commutative-Ring A _)
  left-backward-inclusion-preserves-product-ideal-subset-Commutative-Ring
    {x} {s} {y} Hs
    ( cons (u , (t , Ht) , v) l) =
    is-closed-under-eq-ideal-subset-Commutative-Ring' A
      ( product-subset-Commutative-Ring A S T)
      ( is-closed-under-addition-ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A S T)
        ( is-closed-under-eq-ideal-subset-Commutative-Ring' A
          ( product-subset-Commutative-Ring A S T)
          ( is-closed-under-right-multiplication-ideal-Commutative-Ring A
            ( ideal-subset-Commutative-Ring A
              ( product-subset-Commutative-Ring A S T))
            ( _)
            ( _)
            ( is-closed-under-left-multiplication-ideal-Commutative-Ring A
              ( ideal-subset-Commutative-Ring A
                ( product-subset-Commutative-Ring A S T))
              ( mul-Commutative-Ring A x u)
              ( mul-Commutative-Ring A s t)
              ( contains-subset-ideal-subset-Commutative-Ring A
                ( product-subset-Commutative-Ring A S T)
                ( mul-Commutative-Ring A s t)
                ( unit-trunc-Prop (((s , Hs) , (t , Ht) , refl))))))
          ( ( interchange-mul-mul-Commutative-Ring A _ _ _ _) ∙
            ( ap
              ( mul-Commutative-Ring' A _)
              ( interchange-mul-mul-Commutative-Ring A _ _ _ _))))
        ( left-backward-inclusion-preserves-product-ideal-subset-Commutative-Ring
          Hs l))
      ( left-distributive-mul-add-Commutative-Ring A _ _ _)

  right-backward-inclusion-preserves-product-ideal-subset-Commutative-Ring :
    {u t v : type-Commutative-Ring A} →
    is-in-subset-Commutative-Ring A T t →
    (k : formal-combination-subset-Commutative-Ring A S) →
    is-in-ideal-subset-Commutative-Ring A
      ( product-subset-Commutative-Ring A S T)
      ( mul-Commutative-Ring A
        ( ev-formal-combination-subset-Commutative-Ring A S k)
        ( mul-Commutative-Ring A (mul-Commutative-Ring A u t) v))
  right-backward-inclusion-preserves-product-ideal-subset-Commutative-Ring
    Ht nil =
    is-closed-under-eq-ideal-subset-Commutative-Ring' A
      ( product-subset-Commutative-Ring A S T)
      ( contains-zero-ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A S T))
      ( left-zero-law-mul-Commutative-Ring A _)
  right-backward-inclusion-preserves-product-ideal-subset-Commutative-Ring
    {u} {t} {v} Ht
    ( cons (x , (s , Hs) , y) k) =
    is-closed-under-eq-ideal-subset-Commutative-Ring' A
      ( product-subset-Commutative-Ring A S T)
      ( is-closed-under-addition-ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A S T)
        ( is-closed-under-eq-ideal-subset-Commutative-Ring' A
          ( product-subset-Commutative-Ring A S T)
          ( is-closed-under-right-multiplication-ideal-Commutative-Ring A
            ( ideal-subset-Commutative-Ring A
              ( product-subset-Commutative-Ring A S T))
            ( _)
            ( _)
            ( is-closed-under-left-multiplication-ideal-Commutative-Ring A
              ( ideal-subset-Commutative-Ring A
                ( product-subset-Commutative-Ring A S T))
              ( mul-Commutative-Ring A x u)
              ( mul-Commutative-Ring A s t)
              ( contains-subset-ideal-subset-Commutative-Ring A
                ( product-subset-Commutative-Ring A S T)
                ( mul-Commutative-Ring A s t)
                ( unit-trunc-Prop (((s , Hs) , (t , Ht) , refl))))))
          ( ( interchange-mul-mul-Commutative-Ring A _ _ _ _) ∙
            ( ap
              ( mul-Commutative-Ring' A _)
              ( interchange-mul-mul-Commutative-Ring A _ _ _ _))))
        ( right-backward-inclusion-preserves-product-ideal-subset-Commutative-Ring
          Ht k))
      ( right-distributive-mul-add-Commutative-Ring A _ _ _)

  backward-inclusion-preserves-product-ideal-subset-Commutative-Ring' :
    ( s t : type-Commutative-Ring A)
    ( k : subset-ideal-subset-Commutative-Ring' A S s)
    ( l : subset-ideal-subset-Commutative-Ring' A T t) →
    is-in-ideal-subset-Commutative-Ring A
      ( product-subset-Commutative-Ring A S T)
      ( mul-Commutative-Ring A s t)
  backward-inclusion-preserves-product-ideal-subset-Commutative-Ring' ._ t
    ( nil , refl) l =
    is-closed-under-eq-ideal-subset-Commutative-Ring' A
      ( product-subset-Commutative-Ring A S T)
      ( contains-zero-ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A S T))
      ( left-zero-law-mul-Commutative-Ring A t)
  backward-inclusion-preserves-product-ideal-subset-Commutative-Ring' ._ ._
    ( cons x k , refl) (nil , refl) =
    is-closed-under-eq-ideal-subset-Commutative-Ring' A
      ( product-subset-Commutative-Ring A S T)
      ( contains-zero-ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A S T))
      ( right-zero-law-mul-Commutative-Ring A _)
  backward-inclusion-preserves-product-ideal-subset-Commutative-Ring' ._ ._
    ( cons (x , (s , Hs) , y) k , refl) (cons (u , (t , Ht) , v) l , refl) =
    is-closed-under-eq-ideal-subset-Commutative-Ring' A
      ( product-subset-Commutative-Ring A S T)
      ( is-closed-under-addition-ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A S T)
        ( is-closed-under-addition-ideal-subset-Commutative-Ring A
          ( product-subset-Commutative-Ring A S T)
          ( is-closed-under-eq-ideal-subset-Commutative-Ring' A
            ( product-subset-Commutative-Ring A S T)
            ( is-closed-under-right-multiplication-ideal-Commutative-Ring A
              ( ideal-subset-Commutative-Ring A
                ( product-subset-Commutative-Ring A S T))
              ( _)
              ( _)
              ( is-closed-under-left-multiplication-ideal-Commutative-Ring A
                ( ideal-subset-Commutative-Ring A
                  ( product-subset-Commutative-Ring A S T))
                ( mul-Commutative-Ring A x u)
                ( mul-Commutative-Ring A s t)
                ( contains-subset-ideal-subset-Commutative-Ring A
                  ( product-subset-Commutative-Ring A S T)
                  ( mul-Commutative-Ring A s t)
                  ( unit-trunc-Prop (((s , Hs) , (t , Ht) , refl))))))
            ( ( interchange-mul-mul-Commutative-Ring A _ _ _ _) ∙
              ( ap
                ( mul-Commutative-Ring' A _)
                ( interchange-mul-mul-Commutative-Ring A _ _ _ _))))
          ( left-backward-inclusion-preserves-product-ideal-subset-Commutative-Ring
            Hs l))
        ( is-closed-under-addition-ideal-subset-Commutative-Ring A
          ( product-subset-Commutative-Ring A S T)
          ( right-backward-inclusion-preserves-product-ideal-subset-Commutative-Ring
            Ht k)
          ( backward-inclusion-preserves-product-ideal-subset-Commutative-Ring'
            ( _)
            ( _)
            ( k , refl)
            ( l , refl))))
      ( bidistributive-mul-add-Commutative-Ring A _ _ _ _)

  backward-inclusion-preserves-product-ideal-subset-Commutative-Ring :
    leq-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A
        ( ideal-subset-Commutative-Ring A S)
        ( ideal-subset-Commutative-Ring A T))
      ( ideal-subset-Commutative-Ring A (product-subset-Commutative-Ring A S T))
  backward-inclusion-preserves-product-ideal-subset-Commutative-Ring =
    is-product-product-ideal-Commutative-Ring A
      ( ideal-subset-Commutative-Ring A S)
      ( ideal-subset-Commutative-Ring A T)
      ( ideal-subset-Commutative-Ring A (product-subset-Commutative-Ring A S T))
      ( λ s t p q →
        apply-twice-universal-property-trunc-Prop p q
          ( subset-ideal-subset-Commutative-Ring A
            ( product-subset-Commutative-Ring A S T)
            ( mul-Commutative-Ring A s t))
          ( backward-inclusion-preserves-product-ideal-subset-Commutative-Ring'
            s t))

  preserves-product-ideal-subset-Commutative-Ring :
    ideal-subset-Commutative-Ring A (product-subset-Commutative-Ring A S T) ＝
    product-ideal-Commutative-Ring A
      ( ideal-subset-Commutative-Ring A S)
      ( ideal-subset-Commutative-Ring A T)
  preserves-product-ideal-subset-Commutative-Ring =
    eq-has-same-elements-ideal-Commutative-Ring A
      ( ideal-subset-Commutative-Ring A (product-subset-Commutative-Ring A S T))
      ( product-ideal-Commutative-Ring A
        ( ideal-subset-Commutative-Ring A S)
        ( ideal-subset-Commutative-Ring A T))
      ( λ x →
        forward-inclusion-preserves-product-ideal-subset-Commutative-Ring x ,
        backward-inclusion-preserves-product-ideal-subset-Commutative-Ring x)
```

### `(SI) ＝ (S)I`

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (S : subset-Commutative-Ring l2 A) (I : ideal-Commutative-Ring l3 A)
  where

  forward-inclusion-left-preserves-product-ideal-subset-Commutative-Ring :
    leq-ideal-Commutative-Ring A
      ( ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A S
          ( subset-ideal-Commutative-Ring A I)))
      ( product-ideal-Commutative-Ring A (ideal-subset-Commutative-Ring A S) I)
  forward-inclusion-left-preserves-product-ideal-subset-Commutative-Ring =
    transitive-leq-ideal-Commutative-Ring A
      ( ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A S
          ( subset-ideal-Commutative-Ring A I)))
      ( product-ideal-Commutative-Ring A
        ( ideal-subset-Commutative-Ring A S)
        ( ideal-subset-Commutative-Ring A (subset-ideal-Commutative-Ring A I)))
      ( product-ideal-Commutative-Ring A (ideal-subset-Commutative-Ring A S) I)
      ( preserves-order-right-product-ideal-Commutative-Ring A
        ( ideal-subset-Commutative-Ring A S)
        ( ideal-subset-Commutative-Ring A (subset-ideal-Commutative-Ring A I))
        ( I)
        ( forward-inclusion-idempotent-ideal-subset-Commutative-Ring A I))
      ( forward-inclusion-preserves-product-ideal-subset-Commutative-Ring A S
        ( subset-ideal-Commutative-Ring A I))

  backward-inclusion-left-preserves-product-ideal-subset-Commutative-Ring :
    leq-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A (ideal-subset-Commutative-Ring A S) I)
      ( ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A S
          ( subset-ideal-Commutative-Ring A I)))
  backward-inclusion-left-preserves-product-ideal-subset-Commutative-Ring =
    transitive-leq-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A (ideal-subset-Commutative-Ring A S) I)
      ( product-ideal-Commutative-Ring A
        ( ideal-subset-Commutative-Ring A S)
        ( ideal-subset-Commutative-Ring A (subset-ideal-Commutative-Ring A I)))
      ( ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A S
          ( subset-ideal-Commutative-Ring A I)))
      ( backward-inclusion-preserves-product-ideal-subset-Commutative-Ring A S
        ( subset-ideal-Commutative-Ring A I))
      ( preserves-order-right-product-ideal-Commutative-Ring A
        ( ideal-subset-Commutative-Ring A S)
        ( I)
        ( ideal-subset-Commutative-Ring A (subset-ideal-Commutative-Ring A I))
        ( backward-inclusion-idempotent-ideal-subset-Commutative-Ring A I))

  left-preserves-product-ideal-subset-Commutative-Ring :
    ideal-subset-Commutative-Ring A
      ( product-subset-Commutative-Ring A S
        ( subset-ideal-Commutative-Ring A I)) ＝
    product-ideal-Commutative-Ring A (ideal-subset-Commutative-Ring A S) I
  left-preserves-product-ideal-subset-Commutative-Ring =
    eq-has-same-elements-ideal-Commutative-Ring A
      ( ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A S
          ( subset-ideal-Commutative-Ring A I)))
      ( product-ideal-Commutative-Ring A (ideal-subset-Commutative-Ring A S) I)
      ( λ x →
        forward-inclusion-left-preserves-product-ideal-subset-Commutative-Ring
          x ,
        backward-inclusion-left-preserves-product-ideal-subset-Commutative-Ring
          x)
```

### `(IT) ＝ I(T)`

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 A) (T : subset-Commutative-Ring l3 A)
  where

  forward-inclusion-right-preserves-product-ideal-subset-Commutative-Ring :
    leq-ideal-Commutative-Ring A
      ( ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A
          ( subset-ideal-Commutative-Ring A I)
          ( T)))
      ( product-ideal-Commutative-Ring A I (ideal-subset-Commutative-Ring A T))
  forward-inclusion-right-preserves-product-ideal-subset-Commutative-Ring =
    transitive-leq-ideal-Commutative-Ring A
      ( ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A
          ( subset-ideal-Commutative-Ring A I)
          ( T)))
      ( product-ideal-Commutative-Ring A
        ( ideal-subset-Commutative-Ring A (subset-ideal-Commutative-Ring A I))
        ( ideal-subset-Commutative-Ring A T))
      ( product-ideal-Commutative-Ring A I (ideal-subset-Commutative-Ring A T))
      ( preserves-order-left-product-ideal-Commutative-Ring A
        ( ideal-subset-Commutative-Ring A (subset-ideal-Commutative-Ring A I))
        ( I)
        ( ideal-subset-Commutative-Ring A T)
        ( forward-inclusion-idempotent-ideal-subset-Commutative-Ring A I))
      ( forward-inclusion-preserves-product-ideal-subset-Commutative-Ring A
        ( subset-ideal-Commutative-Ring A I)
        ( T))

  backward-inclusion-right-preserves-product-ideal-subset-Commutative-Ring :
    leq-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A I (ideal-subset-Commutative-Ring A T))
      ( ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A
          ( subset-ideal-Commutative-Ring A I)
          ( T)))
  backward-inclusion-right-preserves-product-ideal-subset-Commutative-Ring =
    transitive-leq-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A I (ideal-subset-Commutative-Ring A T))
      ( product-ideal-Commutative-Ring A
        ( ideal-subset-Commutative-Ring A (subset-ideal-Commutative-Ring A I))
        ( ideal-subset-Commutative-Ring A T))
      ( ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A
          ( subset-ideal-Commutative-Ring A I)
          ( T)))
      ( backward-inclusion-preserves-product-ideal-subset-Commutative-Ring A
        ( subset-ideal-Commutative-Ring A I)
        ( T))
      ( preserves-order-left-product-ideal-Commutative-Ring A
        ( I)
        ( ideal-subset-Commutative-Ring A (subset-ideal-Commutative-Ring A I))
        ( ideal-subset-Commutative-Ring A T)
        ( backward-inclusion-idempotent-ideal-subset-Commutative-Ring A I))

  right-preserves-product-ideal-subset-Commutative-Ring :
    ideal-subset-Commutative-Ring A
      ( product-subset-Commutative-Ring A
        ( subset-ideal-Commutative-Ring A I)
        ( T)) ＝
    product-ideal-Commutative-Ring A I (ideal-subset-Commutative-Ring A T)
  right-preserves-product-ideal-subset-Commutative-Ring =
    eq-has-same-elements-ideal-Commutative-Ring A
      ( ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A
          ( subset-ideal-Commutative-Ring A I)
          ( T)))
      ( product-ideal-Commutative-Ring A I (ideal-subset-Commutative-Ring A T))
      ( λ x →
        forward-inclusion-right-preserves-product-ideal-subset-Commutative-Ring
          x ,
        backward-inclusion-right-preserves-product-ideal-subset-Commutative-Ring
          x)
```

### The product of ideals is associative

Given three ideals `I`, `J`, and `K`, we have that

```text
  (IJ)K ＝ ((generating-subset-product-ideal-Commutative-Ring I J)K)
        ＝ (I(generating-subset-product-ideal-Commutative-Ring J K))
        ＝ I(JK).
```

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 A)
  (J : ideal-Commutative-Ring l3 A)
  (K : ideal-Commutative-Ring l4 A)
  where

  forward-inclusion-associative-product-ideal-Commutative-Ring :
    leq-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A
        ( product-ideal-Commutative-Ring A I J)
        ( K))
      ( product-ideal-Commutative-Ring A
        ( I)
        ( product-ideal-Commutative-Ring A J K))
  forward-inclusion-associative-product-ideal-Commutative-Ring x H =
    forward-inclusion-right-preserves-product-ideal-subset-Commutative-Ring A I
      ( generating-subset-product-ideal-Commutative-Ring A J K)
      ( x)
      ( preserves-order-ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A
          ( product-subset-Commutative-Ring A
            ( subset-ideal-Commutative-Ring A I)
            ( subset-ideal-Commutative-Ring A J))
          ( subset-ideal-Commutative-Ring A K))
        ( product-subset-Commutative-Ring A
          ( subset-ideal-Commutative-Ring A I)
          ( product-subset-Commutative-Ring A
            ( subset-ideal-Commutative-Ring A J)
            ( subset-ideal-Commutative-Ring A K)))
        ( forward-inclusion-associative-product-subset-Commutative-Ring A
          ( subset-ideal-Commutative-Ring A I)
          ( subset-ideal-Commutative-Ring A J)
          ( subset-ideal-Commutative-Ring A K))
        ( x)
        ( backward-inclusion-left-preserves-product-ideal-subset-Commutative-Ring
          ( A)
          ( generating-subset-product-ideal-Commutative-Ring A I J)
          ( K)
          ( x)
          ( H)))

  backward-inclusion-associative-product-ideal-Commutative-Ring :
    leq-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A I
        ( product-ideal-Commutative-Ring A J K))
      ( product-ideal-Commutative-Ring A
        ( product-ideal-Commutative-Ring A I J)
        ( K))
  backward-inclusion-associative-product-ideal-Commutative-Ring x H =
    forward-inclusion-left-preserves-product-ideal-subset-Commutative-Ring A
      ( generating-subset-product-ideal-Commutative-Ring A I J)
      ( K)
      ( x)
      ( preserves-order-ideal-subset-Commutative-Ring A
        ( product-subset-Commutative-Ring A
          ( subset-ideal-Commutative-Ring A I)
          ( product-subset-Commutative-Ring A
            ( subset-ideal-Commutative-Ring A J)
            ( subset-ideal-Commutative-Ring A K)))
        ( product-subset-Commutative-Ring A
          ( product-subset-Commutative-Ring A
            ( subset-ideal-Commutative-Ring A I)
            ( subset-ideal-Commutative-Ring A J))
          ( subset-ideal-Commutative-Ring A K))
        ( backward-inclusion-associative-product-subset-Commutative-Ring A
          ( subset-ideal-Commutative-Ring A I)
          ( subset-ideal-Commutative-Ring A J)
          ( subset-ideal-Commutative-Ring A K))
        ( x)
        ( backward-inclusion-right-preserves-product-ideal-subset-Commutative-Ring
          ( A)
          ( I)
          ( generating-subset-product-ideal-Commutative-Ring A J K)
          ( x)
          ( H)))

  associative-product-ideal-Commutative-Ring :
    product-ideal-Commutative-Ring A (product-ideal-Commutative-Ring A I J) K ＝
    product-ideal-Commutative-Ring A I (product-ideal-Commutative-Ring A J K)
  associative-product-ideal-Commutative-Ring =
    eq-has-same-elements-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A
        ( product-ideal-Commutative-Ring A I J)
        ( K))
      ( product-ideal-Commutative-Ring A I
        ( product-ideal-Commutative-Ring A J K))
      ( λ x →
        forward-inclusion-associative-product-ideal-Commutative-Ring x ,
        backward-inclusion-associative-product-ideal-Commutative-Ring x)
```
