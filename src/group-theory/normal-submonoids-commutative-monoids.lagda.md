# Normal submonoids of commutative monoids

```agda
module group-theory.normal-submonoids-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.congruence-relations-commutative-monoids
open import group-theory.monoids
open import group-theory.saturated-congruence-relations-commutative-monoids
open import group-theory.semigroups
open import group-theory.submonoids-commutative-monoids
open import group-theory.subsets-commutative-monoids
```

</details>

## Idea

A normal submonoid `N` of of a commutative monoid `M` is a submonoid that
corresponds uniquely to a saturated congruence relation `~` on `M` consisting of
the elements congruent to `1`. This is the case if and only if for all `x : M`
and `u : N` we have

```text
  xu ∈ N → x ∈ N
```

## Definitions

### Normal submonoids of commutative monoids

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Submonoid l2 M)
  where

  is-normal-prop-Commutative-Submonoid : Prop (l1 ⊔ l2)
  is-normal-prop-Commutative-Submonoid =
    Π-Prop
      ( type-Commutative-Monoid M)
      ( λ x →
        Π-Prop
          ( type-Commutative-Monoid M)
          ( λ u →
            function-Prop
              ( is-in-Commutative-Submonoid M N u)
              ( function-Prop
                ( is-in-Commutative-Submonoid M N
                  ( mul-Commutative-Monoid M x u))
                ( subset-Commutative-Submonoid M N x))))

  is-normal-Commutative-Submonoid : UU (l1 ⊔ l2)
  is-normal-Commutative-Submonoid =
    type-Prop is-normal-prop-Commutative-Submonoid

  is-prop-is-normal-Commutative-Submonoid :
    is-prop is-normal-Commutative-Submonoid
  is-prop-is-normal-Commutative-Submonoid =
    is-prop-type-Prop is-normal-prop-Commutative-Submonoid

Normal-Commutative-Submonoid :
  {l1 : Level} (l2 : Level) → Commutative-Monoid l1 → UU (l1 ⊔ lsuc l2)
Normal-Commutative-Submonoid l2 M =
  Σ (Commutative-Submonoid l2 M) (is-normal-Commutative-Submonoid M)

module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (N : Normal-Commutative-Submonoid l2 M)
  where

  submonoid-Normal-Commutative-Submonoid : Commutative-Submonoid l2 M
  submonoid-Normal-Commutative-Submonoid = pr1 N

  is-normal-Normal-Commutative-Submonoid :
    is-normal-Commutative-Submonoid M submonoid-Normal-Commutative-Submonoid
  is-normal-Normal-Commutative-Submonoid = pr2 N

  subset-Normal-Commutative-Submonoid : subtype l2 (type-Commutative-Monoid M)
  subset-Normal-Commutative-Submonoid =
    subset-Commutative-Submonoid M submonoid-Normal-Commutative-Submonoid

  is-submonoid-Normal-Commutative-Submonoid :
    is-submonoid-subset-Commutative-Monoid M subset-Normal-Commutative-Submonoid
  is-submonoid-Normal-Commutative-Submonoid =
    is-submonoid-Commutative-Submonoid M submonoid-Normal-Commutative-Submonoid

  is-in-Normal-Commutative-Submonoid : type-Commutative-Monoid M → UU l2
  is-in-Normal-Commutative-Submonoid =
    is-in-Commutative-Submonoid M submonoid-Normal-Commutative-Submonoid

  is-prop-is-in-Normal-Commutative-Submonoid :
    (x : type-Commutative-Monoid M) →
    is-prop (is-in-Normal-Commutative-Submonoid x)
  is-prop-is-in-Normal-Commutative-Submonoid =
    is-prop-is-in-Commutative-Submonoid M
      submonoid-Normal-Commutative-Submonoid

  is-closed-under-eq-Normal-Commutative-Submonoid :
    {x y : type-Commutative-Monoid M} →
    is-in-Normal-Commutative-Submonoid x → (x ＝ y) →
    is-in-Normal-Commutative-Submonoid y
  is-closed-under-eq-Normal-Commutative-Submonoid =
    is-closed-under-eq-subtype subset-Normal-Commutative-Submonoid

  is-closed-under-eq-Normal-Commutative-Submonoid' :
    {x y : type-Commutative-Monoid M} → is-in-Normal-Commutative-Submonoid y →
    (x ＝ y) → is-in-Normal-Commutative-Submonoid x
  is-closed-under-eq-Normal-Commutative-Submonoid' =
    is-closed-under-eq-subtype' subset-Normal-Commutative-Submonoid

  type-Normal-Commutative-Submonoid : UU (l1 ⊔ l2)
  type-Normal-Commutative-Submonoid =
    type-Commutative-Submonoid M submonoid-Normal-Commutative-Submonoid

  is-set-type-Normal-Commutative-Submonoid :
    is-set type-Normal-Commutative-Submonoid
  is-set-type-Normal-Commutative-Submonoid =
    is-set-type-Commutative-Submonoid M submonoid-Normal-Commutative-Submonoid

  set-Normal-Commutative-Submonoid : Set (l1 ⊔ l2)
  set-Normal-Commutative-Submonoid =
    set-Commutative-Submonoid M submonoid-Normal-Commutative-Submonoid

  inclusion-Normal-Commutative-Submonoid :
    type-Normal-Commutative-Submonoid → type-Commutative-Monoid M
  inclusion-Normal-Commutative-Submonoid =
    inclusion-Commutative-Submonoid M submonoid-Normal-Commutative-Submonoid

  ap-inclusion-Normal-Commutative-Submonoid :
    (x y : type-Normal-Commutative-Submonoid) → x ＝ y →
    inclusion-Normal-Commutative-Submonoid x ＝
    inclusion-Normal-Commutative-Submonoid y
  ap-inclusion-Normal-Commutative-Submonoid =
    ap-inclusion-Commutative-Submonoid M submonoid-Normal-Commutative-Submonoid

  is-in-submonoid-inclusion-Normal-Commutative-Submonoid :
    (x : type-Normal-Commutative-Submonoid) →
    is-in-Normal-Commutative-Submonoid
      ( inclusion-Normal-Commutative-Submonoid x)
  is-in-submonoid-inclusion-Normal-Commutative-Submonoid =
    is-in-submonoid-inclusion-Commutative-Submonoid M
      submonoid-Normal-Commutative-Submonoid

  contains-unit-Normal-Commutative-Submonoid :
    is-in-Normal-Commutative-Submonoid (unit-Commutative-Monoid M)
  contains-unit-Normal-Commutative-Submonoid =
    contains-unit-Commutative-Submonoid M submonoid-Normal-Commutative-Submonoid

  unit-Normal-Commutative-Submonoid : type-Normal-Commutative-Submonoid
  unit-Normal-Commutative-Submonoid =
    unit-Commutative-Submonoid M submonoid-Normal-Commutative-Submonoid

  is-closed-under-multiplication-Normal-Commutative-Submonoid :
    {x y : type-Commutative-Monoid M} →
    is-in-Normal-Commutative-Submonoid x →
    is-in-Normal-Commutative-Submonoid y →
    is-in-Normal-Commutative-Submonoid (mul-Commutative-Monoid M x y)
  is-closed-under-multiplication-Normal-Commutative-Submonoid =
    is-closed-under-multiplication-Commutative-Submonoid M
      submonoid-Normal-Commutative-Submonoid

  mul-Normal-Commutative-Submonoid :
    (x y : type-Normal-Commutative-Submonoid) →
    type-Normal-Commutative-Submonoid
  mul-Normal-Commutative-Submonoid =
    mul-Commutative-Submonoid M submonoid-Normal-Commutative-Submonoid

  associative-mul-Normal-Commutative-Submonoid :
    (x y z : type-Normal-Commutative-Submonoid) →
    ( mul-Normal-Commutative-Submonoid
      ( mul-Normal-Commutative-Submonoid x y)
      ( z)) ＝
    ( mul-Normal-Commutative-Submonoid x
      ( mul-Normal-Commutative-Submonoid y z))
  associative-mul-Normal-Commutative-Submonoid =
    associative-mul-Commutative-Submonoid M
      submonoid-Normal-Commutative-Submonoid

  semigroup-Normal-Commutative-Submonoid : Semigroup (l1 ⊔ l2)
  semigroup-Normal-Commutative-Submonoid =
    semigroup-Commutative-Submonoid M submonoid-Normal-Commutative-Submonoid

  left-unit-law-mul-Normal-Commutative-Submonoid :
    (x : type-Normal-Commutative-Submonoid) →
    mul-Normal-Commutative-Submonoid unit-Normal-Commutative-Submonoid x ＝ x
  left-unit-law-mul-Normal-Commutative-Submonoid =
    left-unit-law-mul-Commutative-Submonoid M
      submonoid-Normal-Commutative-Submonoid

  right-unit-law-mul-Normal-Commutative-Submonoid :
    (x : type-Normal-Commutative-Submonoid) →
    mul-Normal-Commutative-Submonoid x unit-Normal-Commutative-Submonoid ＝ x
  right-unit-law-mul-Normal-Commutative-Submonoid =
    right-unit-law-mul-Commutative-Submonoid M
      submonoid-Normal-Commutative-Submonoid

  commutative-mul-Normal-Commutative-Submonoid :
    (x y : type-Normal-Commutative-Submonoid) →
    mul-Normal-Commutative-Submonoid x y ＝
    mul-Normal-Commutative-Submonoid y x
  commutative-mul-Normal-Commutative-Submonoid =
    commutative-mul-Commutative-Submonoid M
      submonoid-Normal-Commutative-Submonoid

  monoid-Normal-Commutative-Submonoid : Monoid (l1 ⊔ l2)
  monoid-Normal-Commutative-Submonoid =
    monoid-Commutative-Submonoid M submonoid-Normal-Commutative-Submonoid

  commutative-monoid-Normal-Commutative-Submonoid :
    Commutative-Monoid (l1 ⊔ l2)
  commutative-monoid-Normal-Commutative-Submonoid =
    commutative-monoid-Commutative-Submonoid M
      submonoid-Normal-Commutative-Submonoid
```

## Properties

### Extensionality of the type of all normal submonoids

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (N : Normal-Commutative-Submonoid l2 M)
  where

  has-same-elements-Normal-Commutative-Submonoid :
    {l3 : Level} → Normal-Commutative-Submonoid l3 M → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Normal-Commutative-Submonoid K =
    has-same-elements-Commutative-Submonoid M
      ( submonoid-Normal-Commutative-Submonoid M N)
      ( submonoid-Normal-Commutative-Submonoid M K)

  extensionality-Normal-Commutative-Submonoid :
    (K : Normal-Commutative-Submonoid l2 M) →
    (N ＝ K) ≃ has-same-elements-Normal-Commutative-Submonoid K
  extensionality-Normal-Commutative-Submonoid =
    extensionality-type-subtype
      ( is-normal-prop-Commutative-Submonoid M)
      ( is-normal-Normal-Commutative-Submonoid M N)
      ( λ x → (id , id))
      ( extensionality-Commutative-Submonoid M
        ( submonoid-Normal-Commutative-Submonoid M N))

  eq-has-same-elements-Normal-Commutative-Submonoid :
    (K : Normal-Commutative-Submonoid l2 M) →
    has-same-elements-Normal-Commutative-Submonoid K → N ＝ K
  eq-has-same-elements-Normal-Commutative-Submonoid K =
    map-inv-equiv (extensionality-Normal-Commutative-Submonoid K)
```

### The congruence relation of a normal submonoid

```agda
module _
  {l1 l2 : Level}
  (M : Commutative-Monoid l1) (N : Normal-Commutative-Submonoid l2 M)
  where

  rel-congruence-Normal-Commutative-Submonoid :
    Relation-Prop (l1 ⊔ l2) (type-Commutative-Monoid M)
  rel-congruence-Normal-Commutative-Submonoid x y =
    Π-Prop
      ( type-Commutative-Monoid M)
      ( λ u →
        iff-Prop
          ( subset-Normal-Commutative-Submonoid M N
            ( mul-Commutative-Monoid M u x))
          ( subset-Normal-Commutative-Submonoid M N
            ( mul-Commutative-Monoid M u y)))

  sim-congruence-Normal-Commutative-Submonoid :
    (x y : type-Commutative-Monoid M) → UU (l1 ⊔ l2)
  sim-congruence-Normal-Commutative-Submonoid x y =
    type-Prop (rel-congruence-Normal-Commutative-Submonoid x y)

  refl-congruence-Normal-Commutative-Submonoid :
    is-reflexive sim-congruence-Normal-Commutative-Submonoid
  pr1 (refl-congruence-Normal-Commutative-Submonoid _ _) = id
  pr2 (refl-congruence-Normal-Commutative-Submonoid _ _) = id

  symmetric-congruence-Normal-Commutative-Submonoid :
    is-symmetric sim-congruence-Normal-Commutative-Submonoid
  pr1 (symmetric-congruence-Normal-Commutative-Submonoid _ _ H u) = pr2 (H u)
  pr2 (symmetric-congruence-Normal-Commutative-Submonoid _ _ H u) = pr1 (H u)

  transitive-congruence-Normal-Commutative-Submonoid :
    is-transitive sim-congruence-Normal-Commutative-Submonoid
  transitive-congruence-Normal-Commutative-Submonoid _ _ _ H K u =
    (H u) ∘iff (K u)

  equivalence-relation-congruence-Normal-Commutative-Submonoid :
    equivalence-relation (l1 ⊔ l2) (type-Commutative-Monoid M)
  pr1 equivalence-relation-congruence-Normal-Commutative-Submonoid =
    rel-congruence-Normal-Commutative-Submonoid
  pr1 (pr2 equivalence-relation-congruence-Normal-Commutative-Submonoid) =
    refl-congruence-Normal-Commutative-Submonoid
  pr1 (pr2 (pr2 equivalence-relation-congruence-Normal-Commutative-Submonoid)) =
    symmetric-congruence-Normal-Commutative-Submonoid
  pr2 (pr2 (pr2 equivalence-relation-congruence-Normal-Commutative-Submonoid)) =
    transitive-congruence-Normal-Commutative-Submonoid

  is-congruence-congruence-Normal-Commutative-Submonoid :
    is-congruence-Commutative-Monoid M
      equivalence-relation-congruence-Normal-Commutative-Submonoid
  pr1
    ( is-congruence-congruence-Normal-Commutative-Submonoid
      {x} {x'} {y} {y'} H K u)
    ( L) =
    is-closed-under-eq-Normal-Commutative-Submonoid M N
      ( forward-implication
        ( K (mul-Commutative-Monoid M u x'))
        ( is-closed-under-eq-Normal-Commutative-Submonoid M N
          ( forward-implication
            ( H (mul-Commutative-Monoid M u y))
            ( is-closed-under-eq-Normal-Commutative-Submonoid M N L
              ( ( inv (associative-mul-Commutative-Monoid M u x y)) ∙
                ( right-swap-mul-Commutative-Monoid M u x y))))
          ( right-swap-mul-Commutative-Monoid M u y x')))
      ( associative-mul-Commutative-Monoid M u x' y')
  pr2
    ( is-congruence-congruence-Normal-Commutative-Submonoid
      {x} {x'} {y} {y'} H K u)
    ( L) =
    is-closed-under-eq-Normal-Commutative-Submonoid M N
      ( backward-implication
        ( K (mul-Commutative-Monoid M u x))
        ( is-closed-under-eq-Normal-Commutative-Submonoid M N
          ( backward-implication
            ( H (mul-Commutative-Monoid M u y'))
            ( is-closed-under-eq-Normal-Commutative-Submonoid M N L
              ( ( inv (associative-mul-Commutative-Monoid M u x' y')) ∙
                ( right-swap-mul-Commutative-Monoid M u x' y'))))
          ( right-swap-mul-Commutative-Monoid M u y' x)))
      ( associative-mul-Commutative-Monoid M u x y)

  congruence-Normal-Commutative-Submonoid :
    congruence-Commutative-Monoid (l1 ⊔ l2) M
  pr1 congruence-Normal-Commutative-Submonoid =
    equivalence-relation-congruence-Normal-Commutative-Submonoid
  pr2 congruence-Normal-Commutative-Submonoid =
    is-congruence-congruence-Normal-Commutative-Submonoid
```

### The normal submonoid obtained from a congruence relation

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R : congruence-Commutative-Monoid l2 M)
  where

  subset-normal-submonoid-congruence-Commutative-Monoid :
    subtype l2 (type-Commutative-Monoid M)
  subset-normal-submonoid-congruence-Commutative-Monoid x =
    prop-congruence-Commutative-Monoid M R x (unit-Commutative-Monoid M)

  is-in-normal-submonoid-congruence-Commutative-Monoid :
    type-Commutative-Monoid M → UU l2
  is-in-normal-submonoid-congruence-Commutative-Monoid =
    is-in-subtype subset-normal-submonoid-congruence-Commutative-Monoid

  contains-unit-normal-submonoid-congruence-Commutative-Monoid :
    is-in-normal-submonoid-congruence-Commutative-Monoid
      ( unit-Commutative-Monoid M)
  contains-unit-normal-submonoid-congruence-Commutative-Monoid =
    refl-congruence-Commutative-Monoid M R (unit-Commutative-Monoid M)

  is-closed-under-multiplication-normal-submonoid-congruence-Commutative-Monoid :
    is-closed-under-multiplication-subset-Commutative-Monoid M
      subset-normal-submonoid-congruence-Commutative-Monoid
  is-closed-under-multiplication-normal-submonoid-congruence-Commutative-Monoid
    x y H K =
    concatenate-sim-eq-congruence-Commutative-Monoid M R
      ( mul-congruence-Commutative-Monoid M R H K)
      ( left-unit-law-mul-Commutative-Monoid M (unit-Commutative-Monoid M))

  submonoid-congruence-Commutative-Monoid : Commutative-Submonoid l2 M
  pr1 submonoid-congruence-Commutative-Monoid =
    subset-normal-submonoid-congruence-Commutative-Monoid
  pr1 (pr2 submonoid-congruence-Commutative-Monoid) =
    contains-unit-normal-submonoid-congruence-Commutative-Monoid
  pr2 (pr2 submonoid-congruence-Commutative-Monoid) =
    is-closed-under-multiplication-normal-submonoid-congruence-Commutative-Monoid

  is-normal-submonoid-congruence-Commutative-Monoid :
    is-normal-Commutative-Submonoid M submonoid-congruence-Commutative-Monoid
  is-normal-submonoid-congruence-Commutative-Monoid x u H K =
    transitive-congruence-Commutative-Monoid M R
      ( x)
      ( mul-Commutative-Monoid M x u)
      ( unit-Commutative-Monoid M)
      ( K)
      ( symmetric-congruence-Commutative-Monoid M R
        ( mul-Commutative-Monoid M x u)
        ( x)
        ( concatenate-sim-eq-congruence-Commutative-Monoid M R
          ( mul-congruence-Commutative-Monoid M R
            ( refl-congruence-Commutative-Monoid M R x)
            ( H))
          ( right-unit-law-mul-Commutative-Monoid M x)))

  normal-submonoid-congruence-Commutative-Monoid :
    Normal-Commutative-Submonoid l2 M
  pr1 normal-submonoid-congruence-Commutative-Monoid =
    submonoid-congruence-Commutative-Monoid
  pr2 normal-submonoid-congruence-Commutative-Monoid =
    is-normal-submonoid-congruence-Commutative-Monoid
```

### The normal submonoid obtained from the congruence relation of a normal submonoid has the same elements as the original normal submonoid

```agda
module _
  {l1 l2 : Level}
  (M : Commutative-Monoid l1) (N : Normal-Commutative-Submonoid l2 M)
  where

  has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoid :
    has-same-elements-Normal-Commutative-Submonoid M
      ( normal-submonoid-congruence-Commutative-Monoid M
        ( congruence-Normal-Commutative-Submonoid M N))
      ( N)
  pr1
    ( has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoid
      x)
    ( H) =
    is-closed-under-eq-Normal-Commutative-Submonoid M N
      ( backward-implication
        ( H (unit-Commutative-Monoid M))
        ( is-closed-under-eq-Normal-Commutative-Submonoid' M N
          ( contains-unit-Normal-Commutative-Submonoid M N)
          ( left-unit-law-mul-Commutative-Monoid M
            ( unit-Commutative-Monoid M))))
      ( left-unit-law-mul-Commutative-Monoid M x)
  pr1
    ( pr2
      ( has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoid
        ( x))
      ( H)
      ( u))
    ( K) =
    is-closed-under-eq-Normal-Commutative-Submonoid' M N
      ( is-normal-Normal-Commutative-Submonoid M N u x H K)
      ( right-unit-law-mul-Commutative-Monoid M u)
  pr2
    ( pr2
      ( has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoid
        ( x))
      ( H)
      ( u))
    ( K) =
    is-closed-under-multiplication-Normal-Commutative-Submonoid M N
      ( is-closed-under-eq-Normal-Commutative-Submonoid M N K
        ( right-unit-law-mul-Commutative-Monoid M u))
      ( H)
```

### The congruence relation of a normal submonoid is saturated

```agda
module _
  {l1 l2 : Level}
  (M : Commutative-Monoid l1) (N : Normal-Commutative-Submonoid l2 M)
  where

  is-saturated-congruence-Normal-Commutative-Submonoid :
    is-saturated-congruence-Commutative-Monoid M
      ( congruence-Normal-Commutative-Submonoid M N)
  is-saturated-congruence-Normal-Commutative-Submonoid x y H u =
    ( ( has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoid
        ( M)
        ( N)
        ( mul-Commutative-Monoid M u y)) ∘iff
      ( H u)) ∘iff
    ( inv-iff
      ( has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoid
        ( M)
        ( N)
        ( mul-Commutative-Monoid M u x)))

  saturated-congruence-Normal-Commutative-Submonoid :
    saturated-congruence-Commutative-Monoid (l1 ⊔ l2) M
  pr1 saturated-congruence-Normal-Commutative-Submonoid =
    congruence-Normal-Commutative-Submonoid M N
  pr2 saturated-congruence-Normal-Commutative-Submonoid =
    is-saturated-congruence-Normal-Commutative-Submonoid
```

### The congruence relation of the normal submonoid associated to a congruence relation relates the same elements as the original congruence relation

```agda
module _
  {l1 l2 : Level}
  (M : Commutative-Monoid l1) (R : saturated-congruence-Commutative-Monoid l2 M)
  where

  normal-submonoid-saturated-congruence-Commutative-Monoid :
    Normal-Commutative-Submonoid l2 M
  normal-submonoid-saturated-congruence-Commutative-Monoid =
    normal-submonoid-congruence-Commutative-Monoid M
      ( congruence-saturated-congruence-Commutative-Monoid M R)

  relate-same-elements-congruence-normal-submonoid-saturated-congruence-Commutative-Monoid :
    relate-same-elements-saturated-congruence-Commutative-Monoid M
      ( saturated-congruence-Normal-Commutative-Submonoid M
        ( normal-submonoid-saturated-congruence-Commutative-Monoid))
      ( R)
  pr1
    ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Commutative-Monoid
      ( x)
      ( y))
    ( H) =
    is-saturated-saturated-congruence-Commutative-Monoid M R x y H
  pr1
    ( pr2
      ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Commutative-Monoid
        ( x)
        ( y))
      ( H)
      ( u)) K =
    transitive-saturated-congruence-Commutative-Monoid M R
      ( mul-Commutative-Monoid M u y)
      ( mul-Commutative-Monoid M u x)
      ( unit-Commutative-Monoid M)
      ( K)
      ( mul-saturated-congruence-Commutative-Monoid M R
        ( refl-saturated-congruence-Commutative-Monoid M R u)
        ( symmetric-saturated-congruence-Commutative-Monoid M R x y H))
  pr2
    ( pr2
      ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Commutative-Monoid
        ( x)
        ( y))
      ( H)
      ( u)) K =
    transitive-saturated-congruence-Commutative-Monoid M R
      ( mul-Commutative-Monoid M u x)
      ( mul-Commutative-Monoid M u y)
      ( unit-Commutative-Monoid M)
      ( K)
      ( mul-saturated-congruence-Commutative-Monoid M R
        ( refl-saturated-congruence-Commutative-Monoid M R u)
        ( H))
```

### The type of normal submonoids of `M` is a retract of the type of congruence relations of `M`

```agda
is-section-congruence-Normal-Commutative-Submonoid :
  {l1 : Level} (l2 : Level) (M : Commutative-Monoid l1)
  (N : Normal-Commutative-Submonoid (l1 ⊔ l2) M) →
  ( normal-submonoid-congruence-Commutative-Monoid M
    ( congruence-Normal-Commutative-Submonoid M N)) ＝
  ( N)
is-section-congruence-Normal-Commutative-Submonoid l2 M N =
  eq-has-same-elements-Normal-Commutative-Submonoid M
    ( normal-submonoid-congruence-Commutative-Monoid M
      ( congruence-Normal-Commutative-Submonoid M N))
    ( N)
    ( has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoid
      M N)

normal-submonoid-retract-of-congruence-Commutative-Monoid :
  {l1 : Level} (l2 : Level) (M : Commutative-Monoid l1) →
  ( Normal-Commutative-Submonoid (l1 ⊔ l2) M) retract-of
  ( congruence-Commutative-Monoid (l1 ⊔ l2) M)
pr1 (normal-submonoid-retract-of-congruence-Commutative-Monoid l2 M) =
  congruence-Normal-Commutative-Submonoid M
pr1 (pr2 (normal-submonoid-retract-of-congruence-Commutative-Monoid l2 M)) =
  normal-submonoid-congruence-Commutative-Monoid M
pr2 (pr2 (normal-submonoid-retract-of-congruence-Commutative-Monoid l2 M)) =
  is-section-congruence-Normal-Commutative-Submonoid l2 M
```

### The type of normal submonoids of `M` is equivalent to the type of saturated congruence relations on `M`

```agda
is-section-saturated-congruence-Normal-Commutative-Submonoid :
  {l1 : Level} (l2 : Level) (M : Commutative-Monoid l1)
  (N : Normal-Commutative-Submonoid (l1 ⊔ l2) M) →
  ( normal-submonoid-saturated-congruence-Commutative-Monoid M
    ( saturated-congruence-Normal-Commutative-Submonoid M N)) ＝
  ( N)
is-section-saturated-congruence-Normal-Commutative-Submonoid l2 M N =
  eq-has-same-elements-Normal-Commutative-Submonoid M
    ( normal-submonoid-saturated-congruence-Commutative-Monoid M
      ( saturated-congruence-Normal-Commutative-Submonoid M N))
    ( N)
    ( has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoid
      M N)

is-retraction-saturated-congruence-Normal-Commutative-Submonoid :
  {l1 : Level} (l2 : Level) (M : Commutative-Monoid l1)
  (R : saturated-congruence-Commutative-Monoid (l1 ⊔ l2) M) →
  ( saturated-congruence-Normal-Commutative-Submonoid M
    ( normal-submonoid-saturated-congruence-Commutative-Monoid M R)) ＝
  ( R)
is-retraction-saturated-congruence-Normal-Commutative-Submonoid l2 M R =
  equivalence-relationate-same-elements-saturated-congruence-Commutative-Monoid
    ( M)
    ( saturated-congruence-Normal-Commutative-Submonoid M
      ( normal-submonoid-saturated-congruence-Commutative-Monoid M R))
    ( R)
    ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Commutative-Monoid
      ( M)
      ( R))

is-equiv-normal-submonoid-saturated-congruence-Commutative-Monoid :
  {l1 : Level} (l2 : Level) (M : Commutative-Monoid l1) →
  is-equiv
    ( normal-submonoid-saturated-congruence-Commutative-Monoid {l2 = l1 ⊔ l2} M)
is-equiv-normal-submonoid-saturated-congruence-Commutative-Monoid l2 M =
  is-equiv-is-invertible
    ( saturated-congruence-Normal-Commutative-Submonoid M)
    ( is-section-saturated-congruence-Normal-Commutative-Submonoid l2 M)
    ( is-retraction-saturated-congruence-Normal-Commutative-Submonoid l2 M)

equiv-normal-submonoid-saturated-congruence-Commutative-Monoid :
  {l1 : Level} (l2 : Level) (M : Commutative-Monoid l1) →
  saturated-congruence-Commutative-Monoid (l1 ⊔ l2) M ≃
  Normal-Commutative-Submonoid (l1 ⊔ l2) M
pr1 (equiv-normal-submonoid-saturated-congruence-Commutative-Monoid l2 M) =
  normal-submonoid-saturated-congruence-Commutative-Monoid M
pr2 (equiv-normal-submonoid-saturated-congruence-Commutative-Monoid l2 M) =
  is-equiv-normal-submonoid-saturated-congruence-Commutative-Monoid l2 M
```
