# Abstract groups

```agda
module group-theory.groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equational-reasoning
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.involutions
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups

open import structured-types.pointed-types
open import structured-types.pointed-types-equipped-with-automorphisms

open import univalent-combinatorics.lists
```

</details>

## Idea

An **abstract group** is a group in the usual algebraic sense, i.e., it consists of a set equipped with a unit element `e`, a binary operation `x, y ↦ xy`, and an inverse operation `x ↦ x⁻¹` satisfying the group laws

```md
  (xy)z = x(yz)      (associativity)
     ex = x          (left unit law)
     xe = x          (right unit law)
   x⁻¹x = e          (left inverse law)
   xx⁻¹ = e          (right inverse law)
```

## Definition

### The condition that a semigroup is a group

```agda
is-group' :
  {l : Level} (G : Semigroup l) → is-unital-Semigroup G → UU l
is-group' G is-unital-Semigroup-G =
  Σ ( type-Semigroup G → type-Semigroup G)
    ( λ i →
      ( (x : type-Semigroup G) →
        Id (mul-Semigroup G (i x) x) (pr1 is-unital-Semigroup-G)) ×
      ( (x : type-Semigroup G) →
        Id (mul-Semigroup G x (i x)) (pr1 is-unital-Semigroup-G)))

is-group :
  {l : Level} (G : Semigroup l) → UU l
is-group G =
  Σ (is-unital-Semigroup G) (is-group' G)
```

### The type of groups

```agda
Group :
  (l : Level) → UU (lsuc l)
Group l = Σ (Semigroup l) is-group

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
    {x x' y y' : type-Group} (p : Id x x') (q : Id y y') →
    Id (mul-Group x y) (mul-Group x' y')
  ap-mul-Group p q = ap-binary mul-Group p q

  mul-Group' : type-Group → type-Group → type-Group
  mul-Group' x y = mul-Group y x

  commute-Group : type-Group → type-Group → UU l
  commute-Group x y = mul-Group x y ＝ mul-Group y x

  associative-mul-Group :
    (x y z : type-Group) →
    Id (mul-Group (mul-Group x y) z) (mul-Group x (mul-Group y z))
  associative-mul-Group = pr2 has-associative-mul-Group

  is-group-Group : is-group semigroup-Group
  is-group-Group = pr2 G

  is-unital-Group : is-unital-Semigroup semigroup-Group
  is-unital-Group = pr1 is-group-Group

  monoid-Group : Monoid l
  pr1 monoid-Group = semigroup-Group
  pr2 monoid-Group = is-unital-Group

  unit-Group : type-Group
  unit-Group = pr1 is-unital-Group

  is-unit-Group : type-Group → UU l
  is-unit-Group x = Id x unit-Group

  is-prop-is-unit-Group : (x : type-Group) → is-prop (is-unit-Group x)
  is-prop-is-unit-Group x = is-set-type-Group x unit-Group

  is-unit-group-Prop : type-Group → Prop l
  pr1 (is-unit-group-Prop x) = is-unit-Group x
  pr2 (is-unit-group-Prop x) = is-prop-is-unit-Group x

  left-unit-law-mul-Group :
    (x : type-Group) → Id (mul-Group unit-Group x) x
  left-unit-law-mul-Group = pr1 (pr2 is-unital-Group)

  right-unit-law-mul-Group :
    (x : type-Group) → Id (mul-Group x unit-Group) x
  right-unit-law-mul-Group = pr2 (pr2 is-unital-Group)

  pointed-type-Group : Pointed-Type l
  pr1 pointed-type-Group = type-Group
  pr2 pointed-type-Group = unit-Group

  has-inverses-Group : is-group' semigroup-Group is-unital-Group
  has-inverses-Group = pr2 is-group-Group

  inv-Group : type-Group → type-Group
  inv-Group = pr1 has-inverses-Group

  left-inverse-law-mul-Group :
    (x : type-Group) → Id (mul-Group (inv-Group x) x) unit-Group
  left-inverse-law-mul-Group = pr1 (pr2 has-inverses-Group)

  right-inverse-law-mul-Group :
    (x : type-Group) → Id (mul-Group x (inv-Group x)) unit-Group
  right-inverse-law-mul-Group = pr2 (pr2 has-inverses-Group)

  inv-unit-Group :
    Id (inv-Group unit-Group) unit-Group
  inv-unit-Group =
    ( inv (left-unit-law-mul-Group (inv-Group unit-Group))) ∙
      ( right-inverse-law-mul-Group unit-Group)
```

## Properties

### Multiplication by `x` from the left is an equivalence

```agda
module _
  {l : Level} (G : Group l)
  where

  left-div-Group : type-Group G → type-Group G → type-Group G
  left-div-Group x y = mul-Group G (inv-Group G x) y

  issec-mul-inv-Group :
    (x : type-Group G) → (mul-Group G x ∘ left-div-Group x) ~ id
  issec-mul-inv-Group x y =
    ( inv (associative-mul-Group G _ _ _)) ∙
    ( ( ap (mul-Group' G y) (right-inverse-law-mul-Group G x)) ∙
      ( left-unit-law-mul-Group G y))

  isretr-mul-inv-Group :
    (x : type-Group G) → (left-div-Group x ∘ mul-Group G x) ~ id
  isretr-mul-inv-Group x y =
    ( inv (associative-mul-Group G _ _ _)) ∙
    ( ( ap (mul-Group' G y) (left-inverse-law-mul-Group G x)) ∙
      ( left-unit-law-mul-Group G y))

  is-equiv-mul-Group : (x : type-Group G) → is-equiv (mul-Group G x)
  is-equiv-mul-Group x =
    is-equiv-has-inverse
      ( left-div-Group x)
      ( issec-mul-inv-Group x)
      ( isretr-mul-inv-Group x)

  equiv-mul-Group : (x : type-Group G) → type-Group G ≃ type-Group G
  pr1 (equiv-mul-Group x) = mul-Group G x
  pr2 (equiv-mul-Group x) = is-equiv-mul-Group x
```

### Multiplication by `x` from the right is an equivalence

```agda
  right-div-Group : type-Group G → type-Group G → type-Group G
  right-div-Group x y = mul-Group G x (inv-Group G y)

  issec-mul-inv-Group' :
    (x : type-Group G) → (mul-Group' G x ∘ (λ y → right-div-Group y x)) ~ id
  issec-mul-inv-Group' x y =
    ( associative-mul-Group G _ _ _) ∙
    ( ( ap (mul-Group G y) (left-inverse-law-mul-Group G x)) ∙
      ( right-unit-law-mul-Group G y))

  isretr-mul-inv-Group' :
    (x : type-Group G) → ((λ y → right-div-Group y x) ∘ mul-Group' G x) ~ id
  isretr-mul-inv-Group' x y =
    ( associative-mul-Group G _ _ _) ∙
    ( ( ap (mul-Group G y) (right-inverse-law-mul-Group G x)) ∙
      ( right-unit-law-mul-Group G y))

  is-equiv-mul-Group' : (x : type-Group G) → is-equiv (mul-Group' G x)
  is-equiv-mul-Group' x =
    is-equiv-has-inverse
      ( λ y → right-div-Group y x)
      ( issec-mul-inv-Group' x)
      ( isretr-mul-inv-Group' x)

  equiv-mul-Group' : (x : type-Group G) → type-Group G ≃ type-Group G
  pr1 (equiv-mul-Group' x) = mul-Group' G x
  pr2 (equiv-mul-Group' x) = is-equiv-mul-Group' x
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
    {x y z : type-Group G} →
    (mul-Group G x y ＝ z) → (x ＝ mul-Group G z (inv-Group G y))
  transpose-eq-mul-Group {x} {y} {z} refl =
    inv (isretr-mul-inv-Group' y x)

  inv-transpose-eq-mul-Group :
    {x y z : type-Group G} →
    (x ＝ mul-Group G z (inv-Group G y)) → (mul-Group G x y ＝ z)
  inv-transpose-eq-mul-Group {._} {y} {z} refl =
    issec-mul-inv-Group' y z

  transpose-eq-mul-Group' :
    {x y z : type-Group G} →
    Id (mul-Group G x y) z → Id y (mul-Group G (inv-Group G x) z)
  transpose-eq-mul-Group' {x} {y} {z} refl =
    inv (isretr-mul-inv-Group x y)

  inv-transpose-eq-mul-Group' :
    {x y z : type-Group G} →
    Id y (mul-Group G (inv-Group G x) z) → (mul-Group G x y ＝ z)
  inv-transpose-eq-mul-Group' {x} {y} {._} refl =
    issec-mul-inv-Group x _
```

### Distributivity of inverses over multiplication

```agda
  distributive-inv-mul-Group :
    (x y : type-Group G) →
    Id (inv-Group G (mul-Group G x y)) (mul-Group G (inv-Group G y) (inv-Group G x))
  distributive-inv-mul-Group x y =
    transpose-eq-mul-Group
      ( ( transpose-eq-mul-Group
          ( ( associative-mul-Group G (inv-Group G (mul-Group G x y)) x y) ∙
            ( left-inverse-law-mul-Group G (mul-Group G x y)))) ∙
        ( left-unit-law-mul-Group G (inv-Group G y)))
```

### Inverting elements of a group is an involution

```agda
  inv-inv-Group :
    (x : type-Group G) → Id (inv-Group G (inv-Group G x)) x
  inv-inv-Group x =
    is-injective-mul-Group
      ( inv-Group G x)
      ( ( right-inverse-law-mul-Group G (inv-Group G x)) ∙
        ( inv (left-inverse-law-mul-Group G x)))
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

### The inverse of `x⁻¹y` is `y⁻¹x`

```agda
  inv-left-div-Group :
    (x y : type-Group G) → inv-Group G (left-div-Group x y) ＝ left-div-Group y x
  inv-left-div-Group x y =
    equational-reasoning
      inv-Group G (left-div-Group x y)
        ＝ left-div-Group y (inv-Group G (inv-Group G x))    by distributive-inv-mul-Group (inv-Group G x) y
        ＝ left-div-Group y x                                by ap (left-div-Group y) (inv-inv-Group x)
```

### The inverse of `xy⁻¹` is `yx⁻¹`

```agda
  inv-right-div-Group :
    (x y : type-Group G) → inv-Group G (right-div-Group x y) ＝ right-div-Group y x
  inv-right-div-Group x y =
    equational-reasoning
      inv-Group G (right-div-Group x y)
        ＝ right-div-Group (inv-Group G (inv-Group G y)) x   by distributive-inv-mul-Group x (inv-Group G y)
        ＝ right-div-Group y x                               by ap (mul-Group' G (inv-Group G x)) (inv-inv-Group y)
```

### The multiple of `x⁻¹y` and `y⁻¹z` is `x⁻¹z`

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
        by ap (mul-Group G (inv-Group G x)) (issec-mul-inv-Group y z)
```

### The multiple of `xy⁻¹` and `yz⁻¹` is `xz⁻¹`

```agda
  mul-right-div-Group :
    (x y z : type-Group G) →
    mul-Group G (right-div-Group x y) (right-div-Group y z) ＝ right-div-Group x z
  mul-right-div-Group x y z =
    equational-reasoning
      mul-Group G (right-div-Group x y) (right-div-Group y z)
      ＝ mul-Group G x (mul-Group G (inv-Group G y) (right-div-Group y z))
        by associative-mul-Group G x (inv-Group G y) (right-div-Group y z)
      ＝ right-div-Group x z
        by ap (mul-Group G x) (isretr-mul-inv-Group y (inv-Group G z))
```

### For any semigroup, being a group is a property

```agda
abstract
  all-elements-equal-is-group :
    {l : Level} (G : Semigroup l) (e : is-unital-Semigroup G) →
    all-elements-equal (is-group' G e)
  all-elements-equal-is-group
    ( pair G (pair μ assoc-G))
    ( pair e (pair left-unit-G right-unit-G))
    ( pair i (pair left-inv-i right-inv-i))
    ( pair i' (pair left-inv-i' right-inv-i')) =
    eq-type-subtype
      ( λ i →
        prod-Prop
          ( Π-Prop (type-Set G) (λ x → Id-Prop G (μ (i x) x) e))
          ( Π-Prop (type-Set G) (λ x → Id-Prop G (μ x (i x)) e)))
      ( eq-htpy
        ( λ x →
          equational-reasoning
          i x ＝ μ e (i x)            by inv (left-unit-G (i x))
              ＝ μ (μ (i' x) x) (i x) by ap (λ y → μ y (i x)) (inv (left-inv-i' x))
              ＝ μ (i' x) (μ x (i x)) by assoc-G (i' x) x (i x)
              ＝ μ (i' x) e           by ap (μ (i' x)) (right-inv-i x)
              ＝ i' x                 by right-unit-G (i' x)))

abstract
  is-prop-is-group :
    {l : Level} (G : Semigroup l) → is-prop (is-group G)
  is-prop-is-group G =
    is-prop-Σ
      ( is-prop-is-unital-Semigroup G)
      ( λ e →
        is-prop-all-elements-equal (all-elements-equal-is-group G e))

is-group-Prop : {l : Level} (G : Semigroup l) → Prop l
pr1 (is-group-Prop G) = is-group G
pr2 (is-group-Prop G) = is-prop-is-group G
```

### Any idempotent element in a group is the unit

```agda
module _
  {l : Level} (G : Group l)
  where

  is-idempotent-Group : type-Group G → UU l
  is-idempotent-Group x = Id (mul-Group G x x) x

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
    Id ( mul-list-Group (concat-list l1 l2))
       ( mul-Group G (mul-list-Group l1) (mul-list-Group l2))
  preserves-concat-mul-list-Group =
    distributive-mul-list-Monoid (monoid-Group G)
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
