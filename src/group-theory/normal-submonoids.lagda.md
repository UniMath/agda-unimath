# Normal submonoids

```agda
module group-theory.normal-submonoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups
open import group-theory.submonoids
```

</details>

## Idea

A normal submonoid `N` of `M` is a monoid that corresponds uniquely to a
congruence relation ~ on `M` consisting of the elements congruent to `1`. This
is the case if and only if for all `x y : M` and `u : N` we have

```md
  xuy ∈ N ⇔ xy ∈ N
```

## Definition

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Submonoid l2 M)
  where

  is-normal-submonoid-Prop : Prop (l1 ⊔ l2)
  is-normal-submonoid-Prop =
    Π-Prop
      ( type-Monoid M)
      ( λ x →
        Π-Prop
          ( type-Monoid M)
          ( λ y →
            Π-Prop
              ( type-Monoid M)
              ( λ u →
                function-Prop
                  ( is-in-Submonoid M N u)
                  ( iff-Prop
                    ( subset-Submonoid M N (mul-Monoid M (mul-Monoid M x u) y))
                    ( subset-Submonoid M N (mul-Monoid M x y))))))

  is-normal-Submonoid : UU (l1 ⊔ l2)
  is-normal-Submonoid = type-Prop is-normal-submonoid-Prop

  is-prop-is-normal-Submonoid : is-prop is-normal-Submonoid
  is-prop-is-normal-Submonoid = is-prop-type-Prop is-normal-submonoid-Prop

Normal-Submonoid :
  {l1 : Level} (l2 : Level) → Monoid l1 → UU (l1 ⊔ lsuc l2)
Normal-Submonoid l2 M = Σ (Submonoid l2 M) (is-normal-Submonoid M)

module _
  {l1 l2 : Level} (M : Monoid l1) (N : Normal-Submonoid l2 M)
  where

  submonoid-Normal-Submonoid : Submonoid l2 M
  submonoid-Normal-Submonoid = pr1 N

  is-normal-Normal-Submonoid : is-normal-Submonoid M submonoid-Normal-Submonoid
  is-normal-Normal-Submonoid = pr2 N

  subset-Normal-Submonoid : subtype l2 (type-Monoid M)
  subset-Normal-Submonoid =
    subset-Submonoid M submonoid-Normal-Submonoid

  is-submonoid-Normal-Submonoid : is-submonoid-Monoid M subset-Normal-Submonoid
  is-submonoid-Normal-Submonoid =
    is-submonoid-Submonoid M submonoid-Normal-Submonoid

  is-in-Normal-Submonoid : type-Monoid M → UU l2
  is-in-Normal-Submonoid =
    is-in-Submonoid M submonoid-Normal-Submonoid

  is-prop-is-in-Normal-Submonoid :
    (x : type-Monoid M) → is-prop (is-in-Normal-Submonoid x)
  is-prop-is-in-Normal-Submonoid =
    is-prop-is-in-Submonoid M submonoid-Normal-Submonoid

  type-Normal-Submonoid : UU (l1 ⊔ l2)
  type-Normal-Submonoid = type-Submonoid M submonoid-Normal-Submonoid

  is-set-type-Normal-Submonoid : is-set type-Normal-Submonoid
  is-set-type-Normal-Submonoid =
    is-set-type-Submonoid M submonoid-Normal-Submonoid

  set-Normal-Submonoid : Set (l1 ⊔ l2)
  set-Normal-Submonoid = set-Submonoid M submonoid-Normal-Submonoid

  inclusion-Normal-Submonoid : type-Normal-Submonoid → type-Monoid M
  inclusion-Normal-Submonoid = inclusion-Submonoid M submonoid-Normal-Submonoid

  ap-inclusion-Normal-Submonoid :
    (x y : type-Normal-Submonoid) → x ＝ y →
    inclusion-Normal-Submonoid x ＝ inclusion-Normal-Submonoid y
  ap-inclusion-Normal-Submonoid =
    ap-inclusion-Submonoid M submonoid-Normal-Submonoid

  is-in-submonoid-inclusion-Normal-Submonoid :
    (x : type-Normal-Submonoid) →
    is-in-Normal-Submonoid (inclusion-Normal-Submonoid x)
  is-in-submonoid-inclusion-Normal-Submonoid =
    is-in-submonoid-inclusion-Submonoid M submonoid-Normal-Submonoid

  contains-unit-Normal-Submonoid : is-in-Normal-Submonoid (unit-Monoid M)
  contains-unit-Normal-Submonoid =
    contains-unit-Submonoid M submonoid-Normal-Submonoid

  unit-Normal-Submonoid : type-Normal-Submonoid
  unit-Normal-Submonoid = unit-Submonoid M submonoid-Normal-Submonoid

  is-closed-under-mul-Normal-Submonoid :
    {x y : type-Monoid M} →
    is-in-Normal-Submonoid x → is-in-Normal-Submonoid y →
    is-in-Normal-Submonoid (mul-Monoid M x y)
  is-closed-under-mul-Normal-Submonoid =
    is-closed-under-mul-Submonoid M submonoid-Normal-Submonoid

  mul-Normal-Submonoid : (x y : type-Normal-Submonoid) → type-Normal-Submonoid
  mul-Normal-Submonoid = mul-Submonoid M submonoid-Normal-Submonoid

  associative-mul-Normal-Submonoid :
    (x y z : type-Normal-Submonoid) →
    (mul-Normal-Submonoid (mul-Normal-Submonoid x y) z) ＝
    (mul-Normal-Submonoid x (mul-Normal-Submonoid y z))
  associative-mul-Normal-Submonoid =
    associative-mul-Submonoid M submonoid-Normal-Submonoid

  semigroup-Normal-Submonoid : Semigroup (l1 ⊔ l2)
  semigroup-Normal-Submonoid =
    semigroup-Submonoid M submonoid-Normal-Submonoid

  left-unit-law-mul-Normal-Submonoid :
    (x : type-Normal-Submonoid) →
    mul-Normal-Submonoid unit-Normal-Submonoid x ＝ x
  left-unit-law-mul-Normal-Submonoid =
    left-unit-law-mul-Submonoid M submonoid-Normal-Submonoid

  right-unit-law-mul-Normal-Submonoid :
    (x : type-Normal-Submonoid) →
    mul-Normal-Submonoid x unit-Normal-Submonoid ＝ x
  right-unit-law-mul-Normal-Submonoid =
    right-unit-law-mul-Submonoid M submonoid-Normal-Submonoid

  monoid-Normal-Submonoid : Monoid (l1 ⊔ l2)
  monoid-Normal-Submonoid = monoid-Submonoid M submonoid-Normal-Submonoid
```

## Properties

### Extensionality of the type of all submonoids

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Normal-Submonoid l2 M)
  where

  has-same-elements-Normal-Submonoid : Normal-Submonoid l2 M → UU (l1 ⊔ l2)
  has-same-elements-Normal-Submonoid K =
    has-same-elements-Submonoid M
      ( submonoid-Normal-Submonoid M N)
      ( submonoid-Normal-Submonoid M K)

  extensionality-Normal-Submonoid :
    (K : Normal-Submonoid l2 M) →
    (N ＝ K) ≃ has-same-elements-Normal-Submonoid K
  extensionality-Normal-Submonoid =
    extensionality-type-subtype
      ( is-normal-submonoid-Prop M)
      ( is-normal-Normal-Submonoid M N)
      ( λ x → (id , id))
      ( extensionality-Submonoid M (submonoid-Normal-Submonoid M N))
```

## References

- S. Margolis and J.-É. Pin, Inverse semigroups and extensions of groups by
  semilattices, J. of Algebra 110 (1987), 277-297.
