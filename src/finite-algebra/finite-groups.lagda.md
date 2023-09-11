# Abstract finite groups

```agda
module finite-algebra.finite-groups where
```

<details><summary>Imports</summary>

```agda
open import finite-algebra.finite-monoids
open import finite-algebra.finite-semigroups

open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.commuting-elements-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import structured-types.pointed-types

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

An **abstract finite group** is a finite group in the usual algebraic sense,
i.e., it consists of a finite type equipped with a unit element `e`, a binary
operation `x, y ↦ xy`, and an inverse operation `x ↦ x⁻¹` satisfying the group
laws

```text
  (xy)z = x(yz)      (associativity)
     ex = x          (left unit law)
     xe = x          (right unit law)
   x⁻¹x = e          (left inverse law)
   xx⁻¹ = e          (right inverse law)
```

## Definition

### The condition that a finite semigroup is a finite group

```agda
is-group-𝔽 :
  {l : Level} (G : Semigroup-𝔽 l) → UU l
is-group-𝔽 G = is-group (semigroup-Semigroup-𝔽 G)
```

### The type of groups

```agda
Group-𝔽 :
  (l : Level) → UU (lsuc l)
Group-𝔽 l = Σ (Semigroup-𝔽 l) is-group-𝔽

compute-group-𝔽 :
  {l : Level} → (G : Group l) → is-finite (type-Group G) → Group-𝔽 l
pr1 (compute-group-𝔽 G f) = compute-semigroup-𝔽 (semigroup-Group G) f
pr2 (compute-group-𝔽 G f) = is-group-Group G

module _
  {l : Level} (G : Group-𝔽 l)
  where

  finite-semigroup-Group-𝔽 : Semigroup-𝔽 l
  finite-semigroup-Group-𝔽 = pr1 G

  semigroup-Group-𝔽 : Semigroup l
  semigroup-Group-𝔽 = semigroup-Semigroup-𝔽 finite-semigroup-Group-𝔽

  is-group-Group-𝔽 : is-group-𝔽 finite-semigroup-Group-𝔽
  is-group-Group-𝔽 = pr2 G

  group-Group-𝔽 : Group l
  pr1 group-Group-𝔽 = semigroup-Group-𝔽
  pr2 group-Group-𝔽 = is-group-Group-𝔽

  finite-type-Group-𝔽 : 𝔽 l
  finite-type-Group-𝔽 = finite-type-Semigroup-𝔽 finite-semigroup-Group-𝔽

  type-Group-𝔽 : UU l
  type-Group-𝔽 = type-Semigroup semigroup-Group-𝔽

  is-finite-type-Group-𝔽 : is-finite type-Group-𝔽
  is-finite-type-Group-𝔽 = is-finite-type-Semigroup-𝔽 finite-semigroup-Group-𝔽

  set-Group-𝔽 : Set l
  set-Group-𝔽 = set-Group group-Group-𝔽

  is-set-type-Group-𝔽 : is-set type-Group-𝔽
  is-set-type-Group-𝔽 = is-set-type-Group group-Group-𝔽

  has-associative-mul-Group-𝔽 : has-associative-mul type-Group-𝔽
  has-associative-mul-Group-𝔽 = has-associative-mul-Group group-Group-𝔽

  mul-Group-𝔽 : type-Group-𝔽 → type-Group-𝔽 → type-Group-𝔽
  mul-Group-𝔽 = mul-Group group-Group-𝔽

  ap-mul-Group-𝔽 :
    {x x' y y' : type-Group-𝔽} (p : Id x x') (q : Id y y') →
    Id (mul-Group-𝔽 x y) (mul-Group-𝔽 x' y')
  ap-mul-Group-𝔽 = ap-mul-Group group-Group-𝔽

  mul-Group-𝔽' : type-Group-𝔽 → type-Group-𝔽 → type-Group-𝔽
  mul-Group-𝔽' = mul-Group' group-Group-𝔽

  commute-Group-𝔽 : type-Group-𝔽 → type-Group-𝔽 → UU l
  commute-Group-𝔽 = commute-Group group-Group-𝔽

  associative-mul-Group-𝔽 :
    (x y z : type-Group-𝔽) →
    Id (mul-Group-𝔽 (mul-Group-𝔽 x y) z) (mul-Group-𝔽 x (mul-Group-𝔽 y z))
  associative-mul-Group-𝔽 = associative-mul-Group group-Group-𝔽

  is-unital-Group-𝔽 : is-unital-Semigroup semigroup-Group-𝔽
  is-unital-Group-𝔽 = is-unital-Group group-Group-𝔽

  monoid-Group-𝔽 : Monoid l
  monoid-Group-𝔽 = monoid-Group group-Group-𝔽

  finite-monoid-Group-𝔽 : Monoid-𝔽 l
  pr1 finite-monoid-Group-𝔽 = finite-semigroup-Group-𝔽
  pr2 finite-monoid-Group-𝔽 = is-unital-Group-𝔽

  unit-Group-𝔽 : type-Group-𝔽
  unit-Group-𝔽 = unit-Group group-Group-𝔽

  is-unit-Group-𝔽 : type-Group-𝔽 → UU l
  is-unit-Group-𝔽 = is-unit-Group group-Group-𝔽

  is-prop-is-unit-Group-𝔽 : (x : type-Group-𝔽) → is-prop (is-unit-Group-𝔽 x)
  is-prop-is-unit-Group-𝔽 = is-prop-is-unit-Group group-Group-𝔽

  is-unit-finite-group-Prop : type-Group-𝔽 → Prop l
  is-unit-finite-group-Prop = is-unit-group-Prop group-Group-𝔽

  left-unit-law-mul-Group-𝔽 :
    (x : type-Group-𝔽) → Id (mul-Group-𝔽 unit-Group-𝔽 x) x
  left-unit-law-mul-Group-𝔽 = left-unit-law-mul-Group group-Group-𝔽

  right-unit-law-mul-Group-𝔽 :
    (x : type-Group-𝔽) → Id (mul-Group-𝔽 x unit-Group-𝔽) x
  right-unit-law-mul-Group-𝔽 = right-unit-law-mul-Group group-Group-𝔽

  pointed-type-Group-𝔽 : Pointed-Type l
  pointed-type-Group-𝔽 = pointed-type-Group group-Group-𝔽

  has-inverses-Group-𝔽 : is-group' semigroup-Group-𝔽 is-unital-Group-𝔽
  has-inverses-Group-𝔽 = has-inverses-Group group-Group-𝔽

  inv-Group-𝔽 : type-Group-𝔽 → type-Group-𝔽
  inv-Group-𝔽 = inv-Group group-Group-𝔽

  left-inverse-law-mul-Group-𝔽 :
    (x : type-Group-𝔽) → Id (mul-Group-𝔽 (inv-Group-𝔽 x) x) unit-Group-𝔽
  left-inverse-law-mul-Group-𝔽 = left-inverse-law-mul-Group group-Group-𝔽

  right-inverse-law-mul-Group-𝔽 :
    (x : type-Group-𝔽) → Id (mul-Group-𝔽 x (inv-Group-𝔽 x)) unit-Group-𝔽
  right-inverse-law-mul-Group-𝔽 = right-inverse-law-mul-Group group-Group-𝔽

  inv-unit-Group-𝔽 :
    Id (inv-Group-𝔽 unit-Group-𝔽) unit-Group-𝔽
  inv-unit-Group-𝔽 = inv-unit-Group group-Group-𝔽
```

## Properties

### There is a finite number of ways to equip a finite type with a structure of group

```agda
module _
  {l : Level}
  (X : 𝔽 l)
  where

  structure-group-𝔽 : UU l
  structure-group-𝔽 =
    Σ (structure-semigroup-𝔽 X) (λ s → is-group-𝔽 (X , s))

  compute-structure-group-𝔽 :
    structure-group-𝔽 → Group-𝔽 l
  pr1 (compute-structure-group-𝔽 (s , g)) = (X , s)
  pr2 (compute-structure-group-𝔽 (s , g)) = g

  is-finite-structure-group-𝔽 :
    is-finite (structure-group-𝔽)
  is-finite-structure-group-𝔽 =
    is-finite-Σ
      ( is-finite-structure-semigroup-𝔽 X)
      ( λ s →
        is-finite-Σ
          ( is-finite-is-unital-Semigroup-𝔽 (X , s))
          ( λ u →
            is-finite-Σ
              ( is-finite-Π
                ( is-finite-type-𝔽 X)
                ( λ _ → is-finite-type-𝔽 X))
              ( λ i →
                is-finite-prod
                  ( is-finite-Π
                    ( is-finite-type-𝔽 X)
                    ( λ x → is-finite-eq-𝔽 X))
                  ( is-finite-Π
                    ( is-finite-type-𝔽 X)
                    ( λ x → is-finite-eq-𝔽 X)))))
```
