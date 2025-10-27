# Subrings

```agda
module ring-theory.subrings where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.monoids
open import group-theory.subgroups-abelian-groups
open import group-theory.submonoids

open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

A
{{#concept "subring" Disambiguation="of a ring" WD="subring" WDID=Q929536 Agda=Subring}}
of a [ring](ring-theory.rings.md) `R` is a
[subset](ring-theory.subsets-rings.md) of `R` that contains the zero and one of
the ring, and is closed under addition, multiplication, and negation.

## Definition

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-subring-prop-subset-Ring : Prop (l1 ⊔ l2)
  is-subring-prop-subset-Ring =
    contains-zero-prop-subset-Ring R S ∧
    contains-one-prop-subset-Ring R S ∧
    is-closed-under-addition-prop-subset-Ring R S ∧
    is-closed-under-negatives-prop-subset-Ring R S ∧
    is-closed-under-multiplication-prop-subset-Ring R S

  is-subring-subset-Ring : UU (l1 ⊔ l2)
  is-subring-subset-Ring = type-Prop is-subring-prop-subset-Ring

Subring : {l1 : Level} (l : Level) → Ring l1 → UU (l1 ⊔ lsuc l)
Subring l R = type-subtype (is-subring-prop-subset-Ring {l2 = l} R)

module _
  {l1 l2 : Level} (R : Ring l1) (S : Subring l2 R)
  where

  subset-Subring : subtype l2 (type-Ring R)
  subset-Subring = pr1 S

  contains-zero-subset-Subring : contains-zero-subset-Ring R subset-Subring
  contains-zero-subset-Subring = pr1 (pr2 S)

  contains-one-subset-Subring : contains-one-subset-Ring R subset-Subring
  contains-one-subset-Subring = pr1 (pr2 (pr2 S))

  is-closed-under-addition-subset-Subring :
    is-closed-under-addition-subset-Ring R subset-Subring
  is-closed-under-addition-subset-Subring = pr1 (pr2 (pr2 (pr2 S)))

  is-closed-under-negatives-subset-Subring :
    is-closed-under-negatives-subset-Ring R subset-Subring
  is-closed-under-negatives-subset-Subring = pr1 (pr2 (pr2 (pr2 (pr2 S))))

  is-closed-under-multiplication-subset-Subring :
    is-closed-under-multiplication-subset-Ring R subset-Subring
  is-closed-under-multiplication-subset-Subring = pr2 (pr2 (pr2 (pr2 (pr2 S))))

  type-Subring : UU (l1 ⊔ l2)
  type-Subring = type-subtype subset-Subring

  ab-Subring : Ab (l1 ⊔ l2)
  ab-Subring =
    ab-Subgroup-Ab
      ( ab-Ring R)
      ( subset-Subring ,
        contains-zero-subset-Subring ,
        is-closed-under-addition-subset-Subring ,
        is-closed-under-negatives-subset-Subring)

  multiplicative-monoid-Subring : Monoid (l1 ⊔ l2)
  multiplicative-monoid-Subring =
    monoid-Submonoid
      ( multiplicative-monoid-Ring R)
      ( subset-Subring ,
        contains-one-subset-Subring ,
        is-closed-under-multiplication-subset-Subring)

  zero-Subring : type-Subring
  zero-Subring = zero-Ab ab-Subring

  one-Subring : type-Subring
  one-Subring = unit-Monoid multiplicative-monoid-Subring

  add-Subring : type-Subring → type-Subring → type-Subring
  add-Subring = add-Ab ab-Subring

  neg-Subring : type-Subring → type-Subring
  neg-Subring = neg-Ab ab-Subring

  mul-Subring : type-Subring → type-Subring → type-Subring
  mul-Subring = mul-Monoid multiplicative-monoid-Subring

  associative-add-Subring :
    (a b c : type-Subring) →
    add-Subring (add-Subring a b) c ＝ add-Subring a (add-Subring b c)
  associative-add-Subring = associative-add-Ab ab-Subring

  left-unit-law-add-Subring :
    (a : type-Subring) → add-Subring zero-Subring a ＝ a
  left-unit-law-add-Subring = left-unit-law-add-Ab ab-Subring

  right-unit-law-add-Subring :
    (a : type-Subring) → add-Subring a zero-Subring ＝ a
  right-unit-law-add-Subring = right-unit-law-add-Ab ab-Subring

  left-inverse-law-add-Subring :
    (a : type-Subring) → add-Subring (neg-Subring a) a ＝ zero-Subring
  left-inverse-law-add-Subring = left-inverse-law-add-Ab ab-Subring

  right-inverse-law-add-Subring :
    (a : type-Subring) → add-Subring a (neg-Subring a) ＝ zero-Subring
  right-inverse-law-add-Subring = right-inverse-law-add-Ab ab-Subring

  associative-mul-Subring :
    (a b c : type-Subring) →
    mul-Subring (mul-Subring a b) c ＝ mul-Subring a (mul-Subring b c)
  associative-mul-Subring = associative-mul-Monoid multiplicative-monoid-Subring

  left-unit-law-mul-Subring :
    (a : type-Subring) → mul-Subring one-Subring a ＝ a
  left-unit-law-mul-Subring =
    left-unit-law-mul-Monoid multiplicative-monoid-Subring

  right-unit-law-mul-Subring :
    (a : type-Subring) → mul-Subring a one-Subring ＝ a
  right-unit-law-mul-Subring =
    right-unit-law-mul-Monoid multiplicative-monoid-Subring

  left-distributive-mul-add-Subring :
    (a b c : type-Subring) →
    mul-Subring a (add-Subring b c) ＝
    add-Subring (mul-Subring a b) (mul-Subring a c)
  left-distributive-mul-add-Subring (a , _) (b , _) (c , _) =
    eq-type-subtype subset-Subring (left-distributive-mul-add-Ring R a b c)

  right-distributive-mul-add-Subring :
    (a b c : type-Subring) →
    mul-Subring (add-Subring a b) c ＝
    add-Subring (mul-Subring a c) (mul-Subring b c)
  right-distributive-mul-add-Subring (a , _) (b , _) (c , _) =
    eq-type-subtype subset-Subring (right-distributive-mul-add-Ring R a b c)

  ring-Subring : Ring (l1 ⊔ l2)
  ring-Subring =
    ( ab-Subring ,
      ( mul-Subring , associative-mul-Subring) ,
      ( one-Subring , left-unit-law-mul-Subring , right-unit-law-mul-Subring) ,
      left-distributive-mul-add-Subring ,
      right-distributive-mul-add-Subring)
```
