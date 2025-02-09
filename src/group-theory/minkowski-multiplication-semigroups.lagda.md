# Minkowski multiplication of semigroup subtypes

```agda
module group-theory.minkowski-multiplication-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

For two [subtypes](foundation-core.subtypes.md) `A`, `B` of a
[semigroup](group-theory.semigroups.md) `S`, the Minkowski multiplication of
`A` and `B` is the set of elements that can be formed by multiplying an element
of `A` and an element of `B`. (This is more usually referred to as a Minkowski
sum, but as the operation on semigroups is referred to as `mul`, we use
multiplicative terminology.)

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (G : Semigroup l1)
  (A : subtype l2 (type-Semigroup G))
  (B : subtype l3 (type-Semigroup G))
  where

  minkowski-mul-Semigroup : subtype (l1 ⊔ l2 ⊔ l3) (type-Semigroup G)
  minkowski-mul-Semigroup c =
    ∃
      ( type-Semigroup G × type-Semigroup G)
      ( λ (a , b) →
        A a ∧ B b ∧ Id-Prop (set-Semigroup G) c (mul-Semigroup G a b))
```

## Properties

### Minkowski multiplication of semigroup subtypes is associative

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Semigroup l1)
  (A : subtype l2 (type-Semigroup G))
  (B : subtype l3 (type-Semigroup G))
  (C : subtype l4 (type-Semigroup G))
  where

  associative-minkowski-mul-has-same-elements-subtype-Semigroup :
    has-same-elements-subtype
      ( minkowski-mul-Semigroup G (minkowski-mul-Semigroup G A B) C)
      ( minkowski-mul-Semigroup G A (minkowski-mul-Semigroup G B C))
  pr1 (associative-minkowski-mul-has-same-elements-subtype-Semigroup x) =
    elim-exists
      ( claim)
      ( λ (ab , c) (ab∈AB , c∈C , x=ab*c) →
        elim-exists
          ( claim)
          ( λ (a , b) (a∈A , b∈B , ab=a*b) →
            intro-exists
              ( a , mul-Semigroup G b c)
              ( a∈A ,
                intro-exists (b , c) (b∈B , c∈C , refl) ,
                ( equational-reasoning
                  x
                  ＝ mul-Semigroup G ab c by x=ab*c
                  ＝ mul-Semigroup G (mul-Semigroup G a b) c
                    by ap (mul-Semigroup' G c) ab=a*b
                  ＝ mul-Semigroup G a (mul-Semigroup G b c)
                    by associative-mul-Semigroup G a b c)))
          ( ab∈AB))
    where
      claim =
        minkowski-mul-Semigroup G A (minkowski-mul-Semigroup G B C) x
  pr2 (associative-minkowski-mul-has-same-elements-subtype-Semigroup x) =
    elim-exists
      ( claim)
      ( λ (a , bc) (a∈A , bc∈BC , x=a*bc) →
        elim-exists
          ( claim)
          ( λ (b , c) (b∈B , c∈C , bc=b*c) →
            intro-exists
              ( mul-Semigroup G a b , c)
              ( intro-exists (a , b) (a∈A , b∈B , refl) ,
                c∈C ,
                ( equational-reasoning
                  x
                  ＝ mul-Semigroup G a bc by x=a*bc
                  ＝ mul-Semigroup G a (mul-Semigroup G b c)
                    by ap (mul-Semigroup G a) bc=b*c
                  ＝ mul-Semigroup G (mul-Semigroup G a b) c
                    by inv (associative-mul-Semigroup G a b c))))
          ( bc∈BC))
    where
      claim =
        minkowski-mul-Semigroup G (minkowski-mul-Semigroup G A B) C x

  associative-minkowski-mul-Semigroup :
    minkowski-mul-Semigroup G (minkowski-mul-Semigroup G A B) C ＝
    minkowski-mul-Semigroup G A (minkowski-mul-Semigroup G B C)
  associative-minkowski-mul-Semigroup =
    eq-has-same-elements-subtype
      ( minkowski-mul-Semigroup G (minkowski-mul-Semigroup G A B) C)
      ( minkowski-mul-Semigroup G A (minkowski-mul-Semigroup G B C))
      ( associative-minkowski-mul-has-same-elements-subtype-Semigroup)
```

### Minkowski multiplication of subtypes of a semigroup forms a semigroup

```agda
module _
  {l : Level}
  (G : Semigroup l)
  where

  semigroup-minkowski-mul-Semigroup : Semigroup (lsuc l)
  pr1 semigroup-minkowski-mul-Semigroup = subtype-Set l (type-Semigroup G)
  pr1 (pr2 semigroup-minkowski-mul-Semigroup) = minkowski-mul-Semigroup G
  pr2 (pr2 semigroup-minkowski-mul-Semigroup) =
    associative-minkowski-mul-Semigroup G
```

## External links

- [Minkowski addition](https://en.wikipedia.org/wiki/Minkowski_addition) at
  Wikipedia
