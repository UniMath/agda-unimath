# Abstract groups

```agda
module group-theory.groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.involutions
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.invertible-elements-monoids
open import group-theory.monoids
open import group-theory.products-of-elements-monoids
open import group-theory.semigroups

open import lists.concatenation-lists
open import lists.lists

open import structured-types.h-spaces
open import structured-types.pointed-types
open import structured-types.pointed-types-equipped-with-automorphisms
```

</details>

## Idea

An **abstract group** is a group in the usual algebraic sense, i.e., it consists
of a set equipped with a unit element `e`, a binary operation `x, y ↦ xy`, and
an inverse operation `x ↦ x⁻¹` satisfying the group laws

```text
  (xy)z = x(yz)      (associativity)
     ex = x          (left unit law)
     xe = x          (right unit law)
   x⁻¹x = e          (left inverse law)
   xx⁻¹ = e          (right inverse law)
```

## Definition

### The condition that a semigroup is a group

```agda
is-group-is-unital-Semigroup :
  {l : Level} (G : Semigroup l) → is-unital-Semigroup G → UU l
is-group-is-unital-Semigroup G is-unital-Semigroup-G =
  Σ ( type-Semigroup G → type-Semigroup G)
    ( λ i →
      ( (x : type-Semigroup G) →
        mul-Semigroup G (i x) x ＝ pr1 is-unital-Semigroup-G) ×
      ( (x : type-Semigroup G) →
        mul-Semigroup G x (i x) ＝ pr1 is-unital-Semigroup-G))

is-group-Semigroup :
  {l : Level} (G : Semigroup l) → UU l
is-group-Semigroup G =
  Σ (is-unital-Semigroup G) (is-group-is-unital-Semigroup G)
```

### The type of groups

```agda
Group :
  (l : Level) → UU (lsuc l)
Group l = Σ (Semigroup l) is-group-Semigroup

module _
  {l : Level} (G : Group l)
  where

  semigroup-Group : Semigroup l
  semigroup-Group = pr1 G

  set-Group : Set l
  set-Group = pr1 semigroup-Group

  type-Group : UU l
  type-Group = pr1 set-Group

  is-set-type-Group : is-set type-Group
  is-set-type-Group = pr2 set-Group

  has-associative-mul-Group : has-associative-mul type-Group
  has-associative-mul-Group = pr2 semigroup-Group

  mul-Group : type-Group → type-Group → type-Group
  mul-Group = pr1 has-associative-mul-Group

  ap-mul-Group :
    {x x' y y' : type-Group} (p : x ＝ x') (q : y ＝ y') →
    mul-Group x y ＝ mul-Group x' y'
  ap-mul-Group p q = ap-binary mul-Group p q

  mul-Group' : type-Group → type-Group → type-Group
  mul-Group' x y = mul-Group y x

  associative-mul-Group :
    (x y z : type-Group) →
    mul-Group (mul-Group x y) z ＝ mul-Group x (mul-Group y z)
  associative-mul-Group = pr2 has-associative-mul-Group

  is-group-Group : is-group-Semigroup semigroup-Group
  is-group-Group = pr2 G

  is-unital-Group : is-unital-Semigroup semigroup-Group
  is-unital-Group = pr1 is-group-Group

  monoid-Group : Monoid l
  pr1 monoid-Group = semigroup-Group
  pr2 monoid-Group = is-unital-Group

  unit-Group : type-Group
  unit-Group = pr1 is-unital-Group

  is-unit-Group : type-Group → UU l
  is-unit-Group x = x ＝ unit-Group

  is-unit-Group' : type-Group → UU l
  is-unit-Group' x = unit-Group ＝ x

  is-prop-is-unit-Group : (x : type-Group) → is-prop (is-unit-Group x)
  is-prop-is-unit-Group x = is-set-type-Group x unit-Group

  is-prop-is-unit-Group' : (x : type-Group) → is-prop (is-unit-Group' x)
  is-prop-is-unit-Group' x = is-set-type-Group unit-Group x

  is-unit-prop-Group : type-Group → Prop l
  pr1 (is-unit-prop-Group x) = is-unit-Group x
  pr2 (is-unit-prop-Group x) = is-prop-is-unit-Group x

  is-unit-prop-Group' : type-Group → Prop l
  pr1 (is-unit-prop-Group' x) = is-unit-Group' x
  pr2 (is-unit-prop-Group' x) = is-prop-is-unit-Group' x

  left-unit-law-mul-Group :
    (x : type-Group) → mul-Group unit-Group x ＝ x
  left-unit-law-mul-Group = pr1 (pr2 is-unital-Group)

  right-unit-law-mul-Group :
    (x : type-Group) → mul-Group x unit-Group ＝ x
  right-unit-law-mul-Group = pr2 (pr2 is-unital-Group)

  coherence-unit-laws-mul-Group :
    left-unit-law-mul-Group unit-Group ＝ right-unit-law-mul-Group unit-Group
  coherence-unit-laws-mul-Group =
    eq-is-prop (is-set-type-Group _ _)

  pointed-type-Group : Pointed-Type l
  pr1 pointed-type-Group = type-Group
  pr2 pointed-type-Group = unit-Group

  h-space-Group : H-Space l
  pr1 h-space-Group = pointed-type-Group
  pr1 (pr2 h-space-Group) = mul-Group
  pr1 (pr2 (pr2 h-space-Group)) = left-unit-law-mul-Group
  pr1 (pr2 (pr2 (pr2 h-space-Group))) = right-unit-law-mul-Group
  pr2 (pr2 (pr2 (pr2 h-space-Group))) = coherence-unit-laws-mul-Group

  has-inverses-Group :
    is-group-is-unital-Semigroup semigroup-Group is-unital-Group
  has-inverses-Group = pr2 is-group-Group

  inv-Group : type-Group → type-Group
  inv-Group = pr1 has-inverses-Group

  left-inverse-law-mul-Group :
    (x : type-Group) → mul-Group (inv-Group x) x ＝ unit-Group
  left-inverse-law-mul-Group = pr1 (pr2 has-inverses-Group)

  right-inverse-law-mul-Group :
    (x : type-Group) → mul-Group x (inv-Group x) ＝ unit-Group
  right-inverse-law-mul-Group = pr2 (pr2 has-inverses-Group)

  is-invertible-element-Group :
    (x : type-Group) → is-invertible-element-Monoid monoid-Group x
  pr1 (is-invertible-element-Group x) = inv-Group x
  pr1 (pr2 (is-invertible-element-Group x)) = right-inverse-law-mul-Group x
  pr2 (pr2 (is-invertible-element-Group x)) = left-inverse-law-mul-Group x

  inv-unit-Group :
    inv-Group unit-Group ＝ unit-Group
  inv-unit-Group =
    ( inv (left-unit-law-mul-Group (inv-Group unit-Group))) ∙
    ( right-inverse-law-mul-Group unit-Group)

  left-swap-mul-Group :
    {x y z : type-Group} → mul-Group x y ＝ mul-Group y x →
    mul-Group x (mul-Group y z) ＝
    mul-Group y (mul-Group x z)
  left-swap-mul-Group =
    left-swap-mul-Semigroup semigroup-Group

  right-swap-mul-Group :
    {x y z : type-Group} → mul-Group y z ＝ mul-Group z y →
    mul-Group (mul-Group x y) z ＝
    mul-Group (mul-Group x z) y
  right-swap-mul-Group =
    right-swap-mul-Semigroup semigroup-Group

  interchange-mul-mul-Group :
    {x y z w : type-Group} → mul-Group y z ＝ mul-Group z y →
    mul-Group (mul-Group x y) (mul-Group z w) ＝
    mul-Group (mul-Group x z) (mul-Group y w)
  interchange-mul-mul-Group =
    interchange-mul-mul-Semigroup semigroup-Group
```

### The structure of a group

```agda
structure-group :
  {l1 : Level} → UU l1 → UU l1
structure-group X =
  Σ ( structure-semigroup X)
    ( λ p → is-group-Semigroup (semigroup-structure-semigroup X p))

group-structure-group :
  {l1 : Level} → (X : UU l1) → structure-group X → Group l1
pr1 (group-structure-group X (p , q)) = semigroup-structure-semigroup X p
pr2 (group-structure-group X (p , q)) = q
```

## Properties

### Multiplication by `x` from the left is an equivalence

```agda
module _
  {l : Level} (G : Group l)
  where

  left-div-Group : type-Group G → type-Group G → type-Group G
  left-div-Group x =
    left-div-is-invertible-element-Monoid
      ( monoid-Group G)
      ( is-invertible-element-Group G x)

  ap-left-div-Group :
    {x x' y y' : type-Group G} → x ＝ x' → y ＝ y' →
    left-div-Group x y ＝ left-div-Group x' y'
  ap-left-div-Group p q = ap-binary left-div-Group p q

  is-section-left-div-Group :
    (x : type-Group G) → (mul-Group G x ∘ left-div-Group x) ~ id
  is-section-left-div-Group x =
    is-section-left-div-is-invertible-element-Monoid
      ( monoid-Group G)
      ( is-invertible-element-Group G x)

  is-retraction-left-div-Group :
    (x : type-Group G) → (left-div-Group x ∘ mul-Group G x) ~ id
  is-retraction-left-div-Group x =
    is-retraction-left-div-is-invertible-element-Monoid
      ( monoid-Group G)
      ( is-invertible-element-Group G x)

  is-equiv-mul-Group : (x : type-Group G) → is-equiv (mul-Group G x)
  is-equiv-mul-Group x =
    is-equiv-mul-is-invertible-element-Monoid
      ( monoid-Group G)
      ( is-invertible-element-Group G x)

  equiv-mul-Group : (x : type-Group G) → type-Group G ≃ type-Group G
  pr1 (equiv-mul-Group x) = mul-Group G x
  pr2 (equiv-mul-Group x) = is-equiv-mul-Group x

  is-equiv-left-div-Group : (x : type-Group G) → is-equiv (left-div-Group x)
  is-equiv-left-div-Group x =
    is-equiv-is-invertible
      ( mul-Group G x)
      ( is-retraction-left-div-Group x)
      ( is-section-left-div-Group x)

  equiv-left-div-Group : (x : type-Group G) → type-Group G ≃ type-Group G
  pr1 (equiv-left-div-Group x) = left-div-Group x
  pr2 (equiv-left-div-Group x) = is-equiv-left-div-Group x
```

### Multiplication by `x` from the right is an equivalence

```agda
  right-div-Group : type-Group G → type-Group G → type-Group G
  right-div-Group x y =
    right-div-is-invertible-element-Monoid
      ( monoid-Group G)
      ( is-invertible-element-Group G y)
      ( x)

  ap-right-div-Group :
    {x x' y y' : type-Group G} → x ＝ x' → y ＝ y' →
    right-div-Group x y ＝ right-div-Group x' y'
  ap-right-div-Group p q = ap-binary right-div-Group p q

  is-section-right-div-Group :
    (x : type-Group G) → (mul-Group' G x ∘ (λ y → right-div-Group y x)) ~ id
  is-section-right-div-Group x =
    is-section-right-div-is-invertible-element-Monoid
      ( monoid-Group G)
      ( is-invertible-element-Group G x)

  is-retraction-right-div-Group :
    (x : type-Group G) → ((λ y → right-div-Group y x) ∘ mul-Group' G x) ~ id
  is-retraction-right-div-Group x =
    is-retraction-right-div-is-invertible-element-Monoid
      ( monoid-Group G)
      ( is-invertible-element-Group G x)

  is-equiv-mul-Group' : (x : type-Group G) → is-equiv (mul-Group' G x)
  is-equiv-mul-Group' x =
    is-equiv-is-invertible
      ( λ y → right-div-Group y x)
      ( is-section-right-div-Group x)
      ( is-retraction-right-div-Group x)

  equiv-mul-Group' : (x : type-Group G) → type-Group G ≃ type-Group G
  pr1 (equiv-mul-Group' x) = mul-Group' G x
  pr2 (equiv-mul-Group' x) = is-equiv-mul-Group' x

  is-equiv-right-div-Group :
    (x : type-Group G) → is-equiv (λ y → right-div-Group y x)
  is-equiv-right-div-Group x =
    is-equiv-is-invertible
      ( mul-Group' G x)
      ( is-retraction-right-div-Group x)
      ( is-section-right-div-Group x)

  equiv-right-div-Group :
    (x : type-Group G) → type-Group G ≃ type-Group G
  pr1 (equiv-right-div-Group x) y = right-div-Group y x
  pr2 (equiv-right-div-Group x) = is-equiv-right-div-Group x
```

### Multiplication is a binary equivalence and a binary embedding

```agda
  is-binary-equiv-mul-Group : is-binary-equiv (mul-Group G)
  pr1 is-binary-equiv-mul-Group = is-equiv-mul-Group'
  pr2 is-binary-equiv-mul-Group = is-equiv-mul-Group

  is-binary-emb-mul-Group : is-binary-emb (mul-Group G)
  is-binary-emb-mul-Group =
    is-binary-emb-is-binary-equiv is-binary-equiv-mul-Group

  is-emb-mul-Group : (x : type-Group G) → is-emb (mul-Group G x)
  is-emb-mul-Group x = is-emb-is-equiv (is-equiv-mul-Group x)

  is-emb-mul-Group' : (x : type-Group G) → is-emb (mul-Group' G x)
  is-emb-mul-Group' x = is-emb-is-equiv (is-equiv-mul-Group' x)

  is-injective-mul-Group : (x : type-Group G) → is-injective (mul-Group G x)
  is-injective-mul-Group x = is-injective-is-equiv (is-equiv-mul-Group x)

  is-injective-mul-Group' : (x : type-Group G) → is-injective (mul-Group' G x)
  is-injective-mul-Group' x = is-injective-is-equiv (is-equiv-mul-Group' x)
```

### Transposition laws for equalities in groups

```agda
  transpose-eq-mul-Group :
    {x y z : type-Group G} → mul-Group G x y ＝ z → x ＝ right-div-Group z y
  transpose-eq-mul-Group {x} {y} {z} refl =
    inv (is-retraction-right-div-Group y x)

  inv-transpose-eq-mul-Group :
    {x y z : type-Group G} → x ＝ right-div-Group z y → mul-Group G x y ＝ z
  inv-transpose-eq-mul-Group {._} {y} {z} refl =
    is-section-right-div-Group y z

  transpose-eq-mul-Group' :
    {x y z : type-Group G} → mul-Group G x y ＝ z → y ＝ left-div-Group x z
  transpose-eq-mul-Group' {x} {y} {z} refl =
    inv (is-retraction-left-div-Group x y)

  inv-transpose-eq-mul-Group' :
    {x y z : type-Group G} → y ＝ left-div-Group x z → mul-Group G x y ＝ z
  inv-transpose-eq-mul-Group' {x} {y} {._} refl =
    is-section-left-div-Group x _

  double-transpose-eq-mul-Group :
    {x y z w : type-Group G} →
    mul-Group G y w ＝ mul-Group G x z →
    left-div-Group x y ＝ right-div-Group z w
  double-transpose-eq-mul-Group p =
    inv
      ( transpose-eq-mul-Group'
        ( inv (transpose-eq-mul-Group p ∙ associative-mul-Group G _ _ _)))

  double-transpose-eq-mul-Group' :
    {x y z w : type-Group G} →
    mul-Group G z x ＝ mul-Group G w y →
    right-div-Group x y ＝ left-div-Group z w
  double-transpose-eq-mul-Group' p =
    inv (double-transpose-eq-mul-Group (inv p))
```

### Distributivity of inverses over multiplication

```agda
  distributive-inv-mul-Group :
    {x y : type-Group G} →
    inv-Group G (mul-Group G x y) ＝
    mul-Group G (inv-Group G y) (inv-Group G x)
  distributive-inv-mul-Group {x} {y} =
    transpose-eq-mul-Group
      ( ( transpose-eq-mul-Group
          ( ( associative-mul-Group G (inv-Group G (mul-Group G x y)) x y) ∙
            ( left-inverse-law-mul-Group G (mul-Group G x y)))) ∙
        ( left-unit-law-mul-Group G (inv-Group G y)))

  distributive-inv-mul-Group' :
    (x y : type-Group G) → mul-Group G x y ＝ mul-Group G y x →
    inv-Group G (mul-Group G x y) ＝ mul-Group G (inv-Group G x) (inv-Group G y)
  distributive-inv-mul-Group' x y H =
    ( distributive-inv-mul-Group) ∙
    ( inv (double-transpose-eq-mul-Group (double-transpose-eq-mul-Group H)))
```

### Inverting elements of a group is an involution

```agda
  inv-inv-Group :
    (x : type-Group G) → inv-Group G (inv-Group G x) ＝ x
  inv-inv-Group x =
    is-injective-mul-Group
      ( inv-Group G x)
      ( ( right-inverse-law-mul-Group G (inv-Group G x)) ∙
        ( inv (left-inverse-law-mul-Group G x)))

  transpose-eq-inv-Group :
    {x y : type-Group G} →
    inv-Group G x ＝ y → x ＝ inv-Group G y
  transpose-eq-inv-Group refl = inv (inv-inv-Group _)

  transpose-eq-inv-Group' :
    {x y : type-Group G} →
    x ＝ inv-Group G y → inv-Group G x ＝ y
  transpose-eq-inv-Group' refl = inv-inv-Group _
```

### Inverting elements of a group is an equivalence

```agda
  is-equiv-inv-Group : is-equiv (inv-Group G)
  is-equiv-inv-Group = is-equiv-is-involution inv-inv-Group

  equiv-equiv-inv-Group : type-Group G ≃ type-Group G
  pr1 equiv-equiv-inv-Group = inv-Group G
  pr2 equiv-equiv-inv-Group = is-equiv-inv-Group
```

### Two elements `x` and `y` are equal iff `x⁻¹y=1`

```agda
  eq-is-unit-left-div-Group :
    {x y : type-Group G} → is-unit-Group G (left-div-Group x y) → x ＝ y
  eq-is-unit-left-div-Group {x} {y} H =
    ( inv (right-unit-law-mul-Group G x)) ∙
    ( inv-transpose-eq-mul-Group' (inv H))

  is-unit-left-div-eq-Group :
    {x y : type-Group G} → x ＝ y → is-unit-Group G (left-div-Group x y)
  is-unit-left-div-eq-Group refl = left-inverse-law-mul-Group G _
```

### Two elements `x` and `y` are equal iff `xy⁻¹=1`

```agda
  eq-is-unit-right-div-Group :
    {x y : type-Group G} → is-unit-Group G (right-div-Group x y) → x ＝ y
  eq-is-unit-right-div-Group H =
    inv (inv-transpose-eq-mul-Group (inv H)) ∙ left-unit-law-mul-Group G _

  is-unit-right-div-eq-Group :
    {x y : type-Group G} → x ＝ y → is-unit-Group G (right-div-Group x y)
  is-unit-right-div-eq-Group refl = right-inverse-law-mul-Group G _
```

### If `xy = 1`, then `y ＝ x⁻¹`

```agda
  abstract
    unique-right-inv-Group :
      (x y : type-Group G) →
      is-unit-Group G (mul-Group G x y) →
      y ＝ inv-Group G x
    unique-right-inv-Group x y xy=1 =
      equational-reasoning
        y
        ＝ left-div-Group x (unit-Group G)
          by transpose-eq-mul-Group' xy=1
        ＝ inv-Group G x
          by right-unit-law-mul-Group G (inv-Group G x)
```

### If `xy = 1`, then `x ＝ y⁻¹`

```agda
  unique-left-inv-Group :
    (x y : type-Group G) →
    is-unit-Group G (mul-Group G x y) →
    x ＝ inv-Group G y
  unique-left-inv-Group x y xy=1 =
    equational-reasoning
      x
      ＝ right-div-Group (unit-Group G) y
        by transpose-eq-mul-Group xy=1
      ＝ inv-Group G y
        by left-unit-law-mul-Group G (inv-Group G y)
```

### The inverse of `x⁻¹y` is `y⁻¹x`

```agda
  inv-left-div-Group :
    (x y : type-Group G) →
    inv-Group G (left-div-Group x y) ＝ left-div-Group y x
  inv-left-div-Group x y =
    equational-reasoning
      inv-Group G (left-div-Group x y)
      ＝ left-div-Group y (inv-Group G (inv-Group G x))
        by distributive-inv-mul-Group
      ＝ left-div-Group y x
        by ap (left-div-Group y) (inv-inv-Group x)
```

### The inverse of `xy⁻¹` is `yx⁻¹`

```agda
  inv-right-div-Group :
    (x y : type-Group G) →
    inv-Group G (right-div-Group x y) ＝ right-div-Group y x
  inv-right-div-Group x y =
    equational-reasoning
      inv-Group G (right-div-Group x y)
      ＝ right-div-Group (inv-Group G (inv-Group G y)) x
        by distributive-inv-mul-Group
      ＝ right-div-Group y x
        by ap (mul-Group' G (inv-Group G x)) (inv-inv-Group y)
```

### The product of `x⁻¹y` and `y⁻¹z` is `x⁻¹z`

```agda
  mul-left-div-Group :
    (x y z : type-Group G) →
    mul-Group G (left-div-Group x y) (left-div-Group y z) ＝ left-div-Group x z
  mul-left-div-Group x y z =
    equational-reasoning
      mul-Group G (left-div-Group x y) (left-div-Group y z)
      ＝ mul-Group G (inv-Group G x) (mul-Group G y (left-div-Group y z))
        by associative-mul-Group G (inv-Group G x) y (left-div-Group y z)
      ＝ left-div-Group x z
        by ap (left-div-Group x) (is-section-left-div-Group y z)
```

### The product of `xy⁻¹` and `yz⁻¹` is `xz⁻¹`

```agda
  mul-right-div-Group :
    (x y z : type-Group G) →
    mul-Group G (right-div-Group x y) (right-div-Group y z) ＝
    right-div-Group x z
  mul-right-div-Group x y z =
    equational-reasoning
      mul-Group G (right-div-Group x y) (right-div-Group y z)
      ＝ mul-Group G x (mul-Group G (inv-Group G y) (right-div-Group y z))
        by associative-mul-Group G x (inv-Group G y) (right-div-Group y z)
      ＝ right-div-Group x z
        by ap (mul-Group G x) (is-retraction-left-div-Group y (inv-Group G z))
```

### For any semigroup, being a group is a property

```agda
abstract
  all-elements-equal-is-group-Semigroup :
    {l : Level} (G : Semigroup l) (e : is-unital-Semigroup G) →
    all-elements-equal (is-group-is-unital-Semigroup G e)
  all-elements-equal-is-group-Semigroup
    ( pair G (pair μ associative-G))
    ( pair e (pair left-unit-G right-unit-G))
    ( pair i (pair left-inv-i right-inv-i))
    ( pair i' (pair left-inv-i' right-inv-i')) =
    eq-type-subtype
      ( λ i →
        product-Prop
          ( Π-Prop (type-Set G) (λ x → Id-Prop G (μ (i x) x) e))
          ( Π-Prop (type-Set G) (λ x → Id-Prop G (μ x (i x)) e)))
      ( eq-htpy
        ( λ x →
          equational-reasoning
          i x
          ＝ μ e (i x)
            by inv (left-unit-G (i x))
          ＝ μ (μ (i' x) x) (i x)
            by ap (λ y → μ y (i x)) (inv (left-inv-i' x))
          ＝ μ (i' x) (μ x (i x))
            by associative-G (i' x) x (i x)
          ＝ μ (i' x) e
            by ap (μ (i' x)) (right-inv-i x)
          ＝ i' x
            by right-unit-G (i' x)))

abstract
  is-prop-is-group-Semigroup :
    {l : Level} (G : Semigroup l) → is-prop (is-group-Semigroup G)
  is-prop-is-group-Semigroup G =
    is-prop-Σ
      ( is-prop-is-unital-Semigroup G)
      ( λ e →
        is-prop-all-elements-equal (all-elements-equal-is-group-Semigroup G e))

is-group-prop-Semigroup : {l : Level} (G : Semigroup l) → Prop l
pr1 (is-group-prop-Semigroup G) = is-group-Semigroup G
pr2 (is-group-prop-Semigroup G) = is-prop-is-group-Semigroup G
```

### Any idempotent element in a group is the unit

```agda
module _
  {l : Level} (G : Group l)
  where

  is-idempotent-Group : type-Group G → UU l
  is-idempotent-Group x = mul-Group G x x ＝ x

  is-unit-is-idempotent-Group :
    {x : type-Group G} → is-idempotent-Group x → is-unit-Group G x
  is-unit-is-idempotent-Group {x} p =
    is-injective-mul-Group G x (p ∙ inv (right-unit-law-mul-Group G x))
```

### Multiplication of a list of elements in a group

```agda
module _
  {l : Level} (G : Group l)
  where

  mul-list-Group : list (type-Group G) → type-Group G
  mul-list-Group = mul-list-Monoid (monoid-Group G)

  preserves-concat-mul-list-Group :
    (l1 l2 : list (type-Group G)) →
    mul-list-Group (concat-list l1 l2) ＝
    mul-Group G (mul-list-Group l1) (mul-list-Group l2)
  preserves-concat-mul-list-Group =
    distributive-mul-concat-list-Monoid (monoid-Group G)
```

### Any group element yields a type equipped with an automorphism

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  pointed-type-with-aut-Group : Pointed-Type-With-Aut l
  pr1 pointed-type-with-aut-Group = pointed-type-Group G
  pr2 pointed-type-with-aut-Group = equiv-mul-Group G g
```
