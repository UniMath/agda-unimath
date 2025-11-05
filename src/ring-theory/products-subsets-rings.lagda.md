# Products of subsets of rings

```agda
module ring-theory.products-subsets-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.universe-levels

open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

The
{{#concept "product" Disambiguation="of two subsets of a ring" Agda=product-subset-Ring}}
of two [subsets](ring-theory.subsets-rings.md) `S` and `T` of a
[ring](ring-theory.rings.md) `R` consists of elements of the form `st` where
`s ∈ S` and `t ∈ T`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (A : Ring l1)
  (S : subset-Ring l2 A) (T : subset-Ring l3 A)
  where

  product-subset-Ring : subset-Ring (l1 ⊔ l2 ⊔ l3) A
  product-subset-Ring x =
    trunc-Prop
      ( Σ ( type-subtype S)
          ( λ s →
            Σ ( type-subtype T)
              ( λ t → x ＝ mul-Ring A (pr1 s) (pr1 t))))
```

## Properties

### Products distribute over unions of families of subsets

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Ring l1) (S : subset-Ring l2 A)
  {I : UU l3} (T : I → subset-Ring l4 A)
  where

  abstract
    forward-inclusion-distributive-product-union-family-of-subsets-Ring :
      product-subset-Ring A S (union-family-of-subtypes T) ⊆
      union-family-of-subtypes (λ i → product-subset-Ring A S (T i))
    forward-inclusion-distributive-product-union-family-of-subsets-Ring x p =
      apply-universal-property-trunc-Prop p
        ( union-family-of-subtypes (λ i → product-subset-Ring A S (T i)) x)
        ( λ where
          ( ( s , Hs) , (t , Ht) , refl) →
            apply-universal-property-trunc-Prop Ht
              ( union-family-of-subtypes
                ( λ i → product-subset-Ring A S (T i))
                ( x))
              ( λ (i , Ht') →
                unit-trunc-Prop
                  ( i , unit-trunc-Prop ((s , Hs) , (t , Ht') , refl))))

  abstract
    backward-inclusion-distributive-product-union-family-of-subsets-Ring :
      union-family-of-subtypes (λ i → product-subset-Ring A S (T i)) ⊆
      product-subset-Ring A S (union-family-of-subtypes T)
    backward-inclusion-distributive-product-union-family-of-subsets-Ring x p =
      apply-universal-property-trunc-Prop p
        ( product-subset-Ring A S (union-family-of-subtypes T) x)
        ( λ (i , u) →
          apply-universal-property-trunc-Prop u
            ( product-subset-Ring A S (union-family-of-subtypes T) x)
            ( λ where
              ( ( s , Hs) , (t , Ht) , refl) →
                unit-trunc-Prop
                  ( (s , Hs) , (t , unit-trunc-Prop (i , Ht)) , refl)))

  distributive-product-union-family-of-subsets-Ring :
    product-subset-Ring A S (union-family-of-subtypes T) ＝
    union-family-of-subtypes (λ i → product-subset-Ring A S (T i))
  distributive-product-union-family-of-subsets-Ring =
    antisymmetric-leq-subtype
      ( product-subset-Ring A S (union-family-of-subtypes T))
      ( union-family-of-subtypes (λ i → product-subset-Ring A S (T i)))
      ( forward-inclusion-distributive-product-union-family-of-subsets-Ring)
      ( backward-inclusion-distributive-product-union-family-of-subsets-Ring)
```

### The product of subsets of commutative rings is associative

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Ring l1)
  (R : subset-Ring l2 A)
  (S : subset-Ring l3 A)
  (T : subset-Ring l4 A)
  where

  abstract
    forward-inclusion-associative-product-subset-Ring :
      ( product-subset-Ring A
        ( product-subset-Ring A R S)
        ( T)) ⊆
      ( product-subset-Ring A
        ( R)
        ( product-subset-Ring A S T))
    forward-inclusion-associative-product-subset-Ring x H =
      apply-universal-property-trunc-Prop H
        ( product-subset-Ring A R
          ( product-subset-Ring A S T)
          ( x))
        ( λ where
          ( ( u , K) , (t , Ht) , refl) →
            apply-universal-property-trunc-Prop K
              ( product-subset-Ring A R
                ( product-subset-Ring A S T)
                ( _))
              ( λ where
                ( ( r , Hr) , (s , Hs) , refl) →
                  unit-trunc-Prop
                    ( ( r , Hr) ,
                      ( ( mul-Ring A s t) ,
                        ( unit-trunc-Prop ((s , Hs) , (t , Ht) , refl))) ,
                      ( associative-mul-Ring A r s t))))

  abstract
    backward-inclusion-associative-product-subset-Ring :
      ( product-subset-Ring A
        ( R)
        ( product-subset-Ring A S T)) ⊆
      ( product-subset-Ring A
        ( product-subset-Ring A R S)
        ( T))
    backward-inclusion-associative-product-subset-Ring x H =
      apply-universal-property-trunc-Prop H
        ( product-subset-Ring A
          ( product-subset-Ring A R S)
          ( T)
          ( x))
        ( λ where
          ( ( r , Hr) , (v , K) , refl) →
            apply-universal-property-trunc-Prop K
              ( product-subset-Ring A
                ( product-subset-Ring A R S)
                ( T)
                ( _))
              ( λ where
                ( ( s , Hs) , (t , Ht) , refl) →
                  unit-trunc-Prop
                    ( ( ( mul-Ring A r s) ,
                        ( unit-trunc-Prop ((r , Hr) , (s , Hs) , refl))) ,
                      ( t , Ht) ,
                      ( inv (associative-mul-Ring A r s t)))))

  associative-product-subset-Ring :
    product-subset-Ring A
      ( product-subset-Ring A R S)
      ( T) ＝
    product-subset-Ring A
      ( R)
      ( product-subset-Ring A S T)
  associative-product-subset-Ring =
    eq-has-same-elements-subtype
      ( product-subset-Ring A
        ( product-subset-Ring A R S)
        ( T))
      ( product-subset-Ring A
        ( R)
        ( product-subset-Ring A S T))
      ( λ x →
        forward-inclusion-associative-product-subset-Ring x ,
        backward-inclusion-associative-product-subset-Ring x)
```

## See also

- [Minkowski multiplication in monoids](group-theory.minkowski-multiplication-monoids.md).
