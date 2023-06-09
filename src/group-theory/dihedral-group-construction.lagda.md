# The dihedral group construction

```agda
module group-theory.dihedral-group-construction where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-coproduct-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

When `A` is an abelian group, we can put a group structure on the disjoint union
`A+A`, which specializes to the dihedral groups when we take `A := ℤ/k`.

## Definitions

```agda
module _
  {l : Level} (A : Ab l)
  where

  set-dihedral-group-Ab : Set l
  set-dihedral-group-Ab = coprod-Set (set-Ab A) (set-Ab A)

  type-dihedral-group-Ab : UU l
  type-dihedral-group-Ab = type-Set set-dihedral-group-Ab

  is-set-type-dihedral-group-Ab : is-set type-dihedral-group-Ab
  is-set-type-dihedral-group-Ab = is-set-type-Set set-dihedral-group-Ab

  unit-dihedral-group-Ab : type-dihedral-group-Ab
  unit-dihedral-group-Ab = inl (zero-Ab A)

  mul-dihedral-group-Ab :
    (x y : type-dihedral-group-Ab) → type-dihedral-group-Ab
  mul-dihedral-group-Ab (inl x) (inl y) = inl (add-Ab A x y)
  mul-dihedral-group-Ab (inl x) (inr y) = inr (add-Ab A (neg-Ab A x) y)
  mul-dihedral-group-Ab (inr x) (inl y) = inr (add-Ab A x y)
  mul-dihedral-group-Ab (inr x) (inr y) = inl (add-Ab A (neg-Ab A x) y)

  inv-dihedral-group-Ab : type-dihedral-group-Ab → type-dihedral-group-Ab
  inv-dihedral-group-Ab (inl x) = inl (neg-Ab A x)
  inv-dihedral-group-Ab (inr x) = inr x

  associative-mul-dihedral-group-Ab :
    (x y z : type-dihedral-group-Ab) →
    (mul-dihedral-group-Ab (mul-dihedral-group-Ab x y) z) ＝
    (mul-dihedral-group-Ab x (mul-dihedral-group-Ab y z))
  associative-mul-dihedral-group-Ab (inl x) (inl y) (inl z) =
    ap inl (associative-add-Ab A x y z)
  associative-mul-dihedral-group-Ab (inl x) (inl y) (inr z) =
    ap
      ( inr)
      ( ( ap (add-Ab' A z) (distributive-neg-add-Ab A x y)) ∙
        ( associative-add-Ab A (neg-Ab A x) (neg-Ab A y) z))
  associative-mul-dihedral-group-Ab (inl x) (inr y) (inl z) =
    ap inr (associative-add-Ab A (neg-Ab A x) y z)
  associative-mul-dihedral-group-Ab (inl x) (inr y) (inr z) =
    ap
      ( inl)
      ( ( ap
          ( add-Ab' A z)
          ( ( distributive-neg-add-Ab A (neg-Ab A x) y) ∙
            ( ap (add-Ab' A (neg-Ab A y)) (neg-neg-Ab A x)))) ∙
        ( associative-add-Ab A x (neg-Ab A y) z))
  associative-mul-dihedral-group-Ab (inr x) (inl y) (inl z) =
    ap inr (associative-add-Ab A x y z)
  associative-mul-dihedral-group-Ab (inr x) (inl y) (inr z) =
    ap
      ( inl)
      ( ( ap (add-Ab' A z) (distributive-neg-add-Ab A x y)) ∙
        ( associative-add-Ab A (neg-Ab A x) (neg-Ab A y) z))
  associative-mul-dihedral-group-Ab (inr x) (inr y) (inl z) =
    ap inl (associative-add-Ab A (neg-Ab A x) y z)
  associative-mul-dihedral-group-Ab (inr x) (inr y) (inr z) =
    ap
      ( inr)
      ( ( ap
          ( add-Ab' A z)
          ( ( distributive-neg-add-Ab A (neg-Ab A x) y) ∙
            ( ap (add-Ab' A (neg-Ab A y)) (neg-neg-Ab A x)))) ∙
        ( associative-add-Ab A x (neg-Ab A y) z))

  left-unit-law-mul-dihedral-group-Ab :
    (x : type-dihedral-group-Ab) →
    (mul-dihedral-group-Ab unit-dihedral-group-Ab x) ＝ x
  left-unit-law-mul-dihedral-group-Ab (inl x) =
    ap inl (left-unit-law-add-Ab A x)
  left-unit-law-mul-dihedral-group-Ab (inr x) =
    ap inr (ap (add-Ab' A x) (neg-zero-Ab A) ∙ left-unit-law-add-Ab A x)

  right-unit-law-mul-dihedral-group-Ab :
    (x : type-dihedral-group-Ab) →
    (mul-dihedral-group-Ab x unit-dihedral-group-Ab) ＝ x
  right-unit-law-mul-dihedral-group-Ab (inl x) =
    ap inl (right-unit-law-add-Ab A x)
  right-unit-law-mul-dihedral-group-Ab (inr x) =
    ap inr (right-unit-law-add-Ab A x)

  left-inverse-law-mul-dihedral-group-Ab :
    (x : type-dihedral-group-Ab) →
    ( mul-dihedral-group-Ab (inv-dihedral-group-Ab x) x) ＝
    ( unit-dihedral-group-Ab)
  left-inverse-law-mul-dihedral-group-Ab (inl x) =
    ap inl (left-inverse-law-add-Ab A x)
  left-inverse-law-mul-dihedral-group-Ab (inr x) =
    ap inl (left-inverse-law-add-Ab A x)

  right-inverse-law-mul-dihedral-group-Ab :
    (x : type-dihedral-group-Ab) →
    ( mul-dihedral-group-Ab x (inv-dihedral-group-Ab x)) ＝
    ( unit-dihedral-group-Ab)
  right-inverse-law-mul-dihedral-group-Ab (inl x) =
    ap inl (right-inverse-law-add-Ab A x)
  right-inverse-law-mul-dihedral-group-Ab (inr x) =
    ap inl (left-inverse-law-add-Ab A x)

  semigroup-dihedral-group-Ab : Semigroup l
  pr1 semigroup-dihedral-group-Ab = set-dihedral-group-Ab
  pr1 (pr2 semigroup-dihedral-group-Ab) = mul-dihedral-group-Ab
  pr2 (pr2 semigroup-dihedral-group-Ab) = associative-mul-dihedral-group-Ab

  monoid-dihedral-group-Ab : Monoid l
  pr1 monoid-dihedral-group-Ab = semigroup-dihedral-group-Ab
  pr1 (pr2 monoid-dihedral-group-Ab) = unit-dihedral-group-Ab
  pr1 (pr2 (pr2 monoid-dihedral-group-Ab)) = left-unit-law-mul-dihedral-group-Ab
  pr2 (pr2 (pr2 monoid-dihedral-group-Ab)) =
    right-unit-law-mul-dihedral-group-Ab

  dihedral-group-Ab : Group l
  pr1 dihedral-group-Ab = semigroup-dihedral-group-Ab
  pr1 (pr1 (pr2 dihedral-group-Ab)) = unit-dihedral-group-Ab
  pr1 (pr2 (pr1 (pr2 dihedral-group-Ab))) = left-unit-law-mul-dihedral-group-Ab
  pr2 (pr2 (pr1 (pr2 dihedral-group-Ab))) = right-unit-law-mul-dihedral-group-Ab
  pr1 (pr2 (pr2 dihedral-group-Ab)) = inv-dihedral-group-Ab
  pr1 (pr2 (pr2 (pr2 dihedral-group-Ab))) =
    left-inverse-law-mul-dihedral-group-Ab
  pr2 (pr2 (pr2 (pr2 dihedral-group-Ab))) =
    right-inverse-law-mul-dihedral-group-Ab
```
