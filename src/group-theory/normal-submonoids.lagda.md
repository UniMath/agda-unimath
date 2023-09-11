# Normal submonoids

```agda
module group-theory.normal-submonoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.retractions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.congruence-relations-monoids
open import group-theory.monoids
open import group-theory.saturated-congruence-relations-monoids
open import group-theory.semigroups
open import group-theory.submonoids
open import group-theory.subsets-monoids
```

</details>

## Idea

A **normal submonoid** `N` of `M` is a monoid for which there exists a
congruence relation `~` on `M` such that the elements of `N` are precisely the
elements `x ~ 1`. Such a congruence relation is rarely unique. However, one can
show that the normal submonoids form a retract of the type of congruence
relations on `M`, and that the normal submonoids correspond uniquely to
_saturated_ congruence relations.

A submonoid `N` of `M` is normal if and only if for all `x y : M` and `u : N` we
have

```text
  xuy ∈ N ⇔ xy ∈ N.
```

## Definitions

### Normal submonoids

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

  is-closed-under-eq-Normal-Submonoid :
    {x y : type-Monoid M} → is-in-Normal-Submonoid x → (x ＝ y) →
    is-in-Normal-Submonoid y
  is-closed-under-eq-Normal-Submonoid =
    is-closed-under-eq-subtype subset-Normal-Submonoid

  is-closed-under-eq-Normal-Submonoid' :
    {x y : type-Monoid M} → is-in-Normal-Submonoid y →
    (x ＝ y) → is-in-Normal-Submonoid x
  is-closed-under-eq-Normal-Submonoid' =
    is-closed-under-eq-subtype' subset-Normal-Submonoid

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

  is-closed-under-multiplication-Normal-Submonoid :
    {x y : type-Monoid M} →
    is-in-Normal-Submonoid x → is-in-Normal-Submonoid y →
    is-in-Normal-Submonoid (mul-Monoid M x y)
  is-closed-under-multiplication-Normal-Submonoid =
    is-closed-under-multiplication-Submonoid M submonoid-Normal-Submonoid

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

### Extensionality of the type of all normal submonoids

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Normal-Submonoid l2 M)
  where

  has-same-elements-Normal-Submonoid :
    {l3 : Level} → Normal-Submonoid l3 M → UU (l1 ⊔ l2 ⊔ l3)
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

  eq-has-same-elements-Normal-Submonoid :
    (K : Normal-Submonoid l2 M) →
    has-same-elements-Normal-Submonoid K → N ＝ K
  eq-has-same-elements-Normal-Submonoid K =
    map-inv-equiv (extensionality-Normal-Submonoid K)
```

### The congruence relation of a normal submonoid

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Normal-Submonoid l2 M)
  where

  rel-congruence-Normal-Submonoid : Relation-Prop (l1 ⊔ l2) (type-Monoid M)
  rel-congruence-Normal-Submonoid x y =
    Π-Prop
      ( type-Monoid M)
      ( λ u →
        Π-Prop
          ( type-Monoid M)
          ( λ v →
            iff-Prop
              ( subset-Normal-Submonoid M N
                ( mul-Monoid M (mul-Monoid M u x) v))
              ( subset-Normal-Submonoid M N
                ( mul-Monoid M (mul-Monoid M u y) v))))

  sim-congruence-Normal-Submonoid : (x y : type-Monoid M) → UU (l1 ⊔ l2)
  sim-congruence-Normal-Submonoid x y =
    type-Prop (rel-congruence-Normal-Submonoid x y)

  refl-congruence-Normal-Submonoid :
    is-reflexive sim-congruence-Normal-Submonoid
  pr1 (refl-congruence-Normal-Submonoid _ u v) = id
  pr2 (refl-congruence-Normal-Submonoid _ u v) = id

  symmetric-congruence-Normal-Submonoid :
    is-symmetric sim-congruence-Normal-Submonoid
  pr1 (symmetric-congruence-Normal-Submonoid _ _ H u v) = pr2 (H u v)
  pr2 (symmetric-congruence-Normal-Submonoid _ _ H u v) = pr1 (H u v)

  transitive-congruence-Normal-Submonoid :
    is-transitive sim-congruence-Normal-Submonoid
  transitive-congruence-Normal-Submonoid _ _ _ H K u v = (H u v) ∘iff (K u v)

  eq-rel-congruence-Normal-Submonoid :
    Equivalence-Relation (l1 ⊔ l2) (type-Monoid M)
  pr1 eq-rel-congruence-Normal-Submonoid = rel-congruence-Normal-Submonoid
  pr1 (pr2 eq-rel-congruence-Normal-Submonoid) =
    refl-congruence-Normal-Submonoid
  pr1 (pr2 (pr2 eq-rel-congruence-Normal-Submonoid)) =
    symmetric-congruence-Normal-Submonoid
  pr2 (pr2 (pr2 eq-rel-congruence-Normal-Submonoid)) =
    transitive-congruence-Normal-Submonoid

  is-congruence-congruence-Normal-Submonoid :
    is-congruence-Monoid M eq-rel-congruence-Normal-Submonoid
  pr1 (is-congruence-congruence-Normal-Submonoid {x} {x'} {y} {y'} H K u v) L =
    is-closed-under-eq-Normal-Submonoid M N
      ( forward-implication
        ( H u (mul-Monoid M y' v))
        ( is-closed-under-eq-Normal-Submonoid M N
          ( forward-implication
            ( K (mul-Monoid M u x) v)
            ( is-closed-under-eq-Normal-Submonoid M N L
              ( ap (mul-Monoid' M v) (inv (associative-mul-Monoid M u x y)))))
          ( associative-mul-Monoid M (mul-Monoid M u x) y' v)))
      ( ( inv (associative-mul-Monoid M (mul-Monoid M u x') y' v)) ∙
        ( ap (mul-Monoid' M v) (associative-mul-Monoid M u x' y')))
  pr2 (is-congruence-congruence-Normal-Submonoid {x} {x'} {y} {y'} H K u v) L =
    is-closed-under-eq-Normal-Submonoid M N
      ( backward-implication
        ( H u (mul-Monoid M y v))
        ( is-closed-under-eq-Normal-Submonoid M N
          ( backward-implication
            ( K (mul-Monoid M u x') v)
            ( is-closed-under-eq-Normal-Submonoid M N L
              ( ap (mul-Monoid' M v) (inv (associative-mul-Monoid M u x' y')))))
          ( associative-mul-Monoid M (mul-Monoid M u x') y v)))
      ( ( inv (associative-mul-Monoid M (mul-Monoid M u x) y v)) ∙
        ( ap (mul-Monoid' M v) (associative-mul-Monoid M u x y)))

  congruence-Normal-Submonoid : congruence-Monoid (l1 ⊔ l2) M
  pr1 congruence-Normal-Submonoid = eq-rel-congruence-Normal-Submonoid
  pr2 congruence-Normal-Submonoid = is-congruence-congruence-Normal-Submonoid
```

### The normal submonoid obtained from a congruence relation

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (R : congruence-Monoid l2 M)
  where

  subset-normal-submonoid-congruence-Monoid :
    subtype l2 (type-Monoid M)
  subset-normal-submonoid-congruence-Monoid x =
    prop-congruence-Monoid M R x (unit-Monoid M)

  is-in-normal-submonoid-congruence-Monoid : type-Monoid M → UU l2
  is-in-normal-submonoid-congruence-Monoid =
    is-in-subtype subset-normal-submonoid-congruence-Monoid

  contains-unit-normal-submonoid-congruence-Monoid :
    is-in-normal-submonoid-congruence-Monoid (unit-Monoid M)
  contains-unit-normal-submonoid-congruence-Monoid =
    refl-congruence-Monoid M R (unit-Monoid M)

  is-closed-under-multiplication-normal-submonoid-congruence-Monoid :
    is-closed-under-multiplication-subset-Monoid M
      subset-normal-submonoid-congruence-Monoid
  is-closed-under-multiplication-normal-submonoid-congruence-Monoid x y H K =
    concatenate-sim-eq-congruence-Monoid M R
      ( mul-congruence-Monoid M R H K)
      ( left-unit-law-mul-Monoid M (unit-Monoid M))

  submonoid-congruence-Monoid : Submonoid l2 M
  pr1 submonoid-congruence-Monoid = subset-normal-submonoid-congruence-Monoid
  pr1 (pr2 submonoid-congruence-Monoid) =
    contains-unit-normal-submonoid-congruence-Monoid
  pr2 (pr2 submonoid-congruence-Monoid) =
    is-closed-under-multiplication-normal-submonoid-congruence-Monoid

  is-normal-submonoid-congruence-Monoid :
    is-normal-Submonoid M submonoid-congruence-Monoid
  pr1 (is-normal-submonoid-congruence-Monoid x y u H) K =
    transitive-congruence-Monoid M R
      ( mul-Monoid M x y)
      ( mul-Monoid M (mul-Monoid M x u) y)
      ( unit-Monoid M)
      ( K)
      ( symmetric-congruence-Monoid M R
        ( mul-Monoid M (mul-Monoid M x u) y)
        ( mul-Monoid M x y)
        ( mul-congruence-Monoid M R
          ( concatenate-sim-eq-congruence-Monoid M R
            ( mul-congruence-Monoid M R (refl-congruence-Monoid M R x) H)
            ( right-unit-law-mul-Monoid M x))
          ( refl-congruence-Monoid M R y)))
  pr2 (is-normal-submonoid-congruence-Monoid x y u H) K =
    transitive-congruence-Monoid M R
      ( mul-Monoid M (mul-Monoid M x u) y)
      ( mul-Monoid M x y)
      ( unit-Monoid M)
      ( K)
      ( mul-congruence-Monoid M R
        ( concatenate-sim-eq-congruence-Monoid M R
          ( mul-congruence-Monoid M R (refl-congruence-Monoid M R x) H)
          ( right-unit-law-mul-Monoid M x))
        ( refl-congruence-Monoid M R y))

  normal-submonoid-congruence-Monoid : Normal-Submonoid l2 M
  pr1 normal-submonoid-congruence-Monoid = submonoid-congruence-Monoid
  pr2 normal-submonoid-congruence-Monoid = is-normal-submonoid-congruence-Monoid
```

### The normal submonoid obtained from the congruence relation of a normal submonoid has the same elements as the original normal submonoid

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Normal-Submonoid l2 M)
  where

  has-same-elements-normal-submonoid-congruence-Normal-Submonoid :
    has-same-elements-Normal-Submonoid M
      ( normal-submonoid-congruence-Monoid M
        ( congruence-Normal-Submonoid M N))
      ( N)
  pr1 (has-same-elements-normal-submonoid-congruence-Normal-Submonoid x) H =
    is-closed-under-eq-Normal-Submonoid M N
      ( backward-implication
        ( H (unit-Monoid M) (unit-Monoid M))
        ( is-closed-under-eq-Normal-Submonoid' M N
          ( contains-unit-Normal-Submonoid M N)
          ( ( right-unit-law-mul-Monoid M
              ( mul-Monoid M (unit-Monoid M) (unit-Monoid M))) ∙
            ( left-unit-law-mul-Monoid M (unit-Monoid M)))))
      ( right-unit-law-mul-Monoid M _ ∙ left-unit-law-mul-Monoid M _)
  pr1
    ( pr2
      ( has-same-elements-normal-submonoid-congruence-Normal-Submonoid x)
      ( H)
      ( u)
      ( v))
    ( K) =
    is-closed-under-eq-Normal-Submonoid' M N
      ( forward-implication (is-normal-Normal-Submonoid M N u v x H) K)
      ( ap (mul-Monoid' M v) (right-unit-law-mul-Monoid M u))
  pr2
    ( pr2
      ( has-same-elements-normal-submonoid-congruence-Normal-Submonoid x)
      ( H)
      ( u)
      ( v))
    ( K) =
    backward-implication
      ( is-normal-Normal-Submonoid M N u v x H)
      ( is-closed-under-eq-Normal-Submonoid M N K
        ( ap (mul-Monoid' M v) (right-unit-law-mul-Monoid M u)))
```

### The congruence relation of a normal submonoid is saturated

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Normal-Submonoid l2 M)
  where

  is-saturated-congruence-Normal-Submonoid :
    is-saturated-congruence-Monoid M (congruence-Normal-Submonoid M N)
  is-saturated-congruence-Normal-Submonoid x y H u v =
    ( ( has-same-elements-normal-submonoid-congruence-Normal-Submonoid M N
        ( mul-Monoid M (mul-Monoid M u y) v)) ∘iff
      ( H u v)) ∘iff
    ( inv-iff
      ( has-same-elements-normal-submonoid-congruence-Normal-Submonoid M N
        ( mul-Monoid M (mul-Monoid M u x) v)))

  saturated-congruence-Normal-Submonoid :
    saturated-congruence-Monoid (l1 ⊔ l2) M
  pr1 saturated-congruence-Normal-Submonoid = congruence-Normal-Submonoid M N
  pr2 saturated-congruence-Normal-Submonoid =
    is-saturated-congruence-Normal-Submonoid
```

### The congruence relation of the normal submonoid associated to a congruence relation relates the same elements as the original congruence relation

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (R : saturated-congruence-Monoid l2 M)
  where

  normal-submonoid-saturated-congruence-Monoid :
    Normal-Submonoid l2 M
  normal-submonoid-saturated-congruence-Monoid =
    normal-submonoid-congruence-Monoid M
      ( congruence-saturated-congruence-Monoid M R)

  relate-same-elements-congruence-normal-submonoid-saturated-congruence-Monoid :
    relate-same-elements-saturated-congruence-Monoid M
      ( saturated-congruence-Normal-Submonoid M
        ( normal-submonoid-saturated-congruence-Monoid))
      ( R)
  pr1
    ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Monoid
      x y)
    H =
    is-saturated-saturated-congruence-Monoid M R x y H
  pr1
    ( pr2
      ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Monoid
        x y)
      H u v) K =
    transitive-saturated-congruence-Monoid M R
      ( mul-Monoid M (mul-Monoid M u y) v)
      ( mul-Monoid M (mul-Monoid M u x) v)
      ( unit-Monoid M)
      ( K)
      ( mul-saturated-congruence-Monoid M R
        ( mul-saturated-congruence-Monoid M R
          ( refl-saturated-congruence-Monoid M R u)
          ( symmetric-saturated-congruence-Monoid M R x y H))
        ( refl-saturated-congruence-Monoid M R v))
  pr2
    ( pr2
      ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Monoid
        x y)
      H u v) K =
    transitive-saturated-congruence-Monoid M R
      ( mul-Monoid M (mul-Monoid M u x) v)
      ( mul-Monoid M (mul-Monoid M u y) v)
      ( unit-Monoid M)
      ( K)
      ( mul-saturated-congruence-Monoid M R
        ( mul-saturated-congruence-Monoid M R
          ( refl-saturated-congruence-Monoid M R u)
          ( H))
        ( refl-saturated-congruence-Monoid M R v))
```

### The type of normal submonoids of `M` is a retract of the type of congruence relations of `M`

```agda
is-section-congruence-Normal-Submonoid :
  {l1 : Level} (l2 : Level) (M : Monoid l1) (N : Normal-Submonoid (l1 ⊔ l2) M) →
  ( normal-submonoid-congruence-Monoid M (congruence-Normal-Submonoid M N)) ＝
  ( N)
is-section-congruence-Normal-Submonoid l2 M N =
  eq-has-same-elements-Normal-Submonoid M
    ( normal-submonoid-congruence-Monoid M (congruence-Normal-Submonoid M N))
    ( N)
    ( has-same-elements-normal-submonoid-congruence-Normal-Submonoid M N)

normal-submonoid-retract-of-congruence-Monoid :
  {l1 : Level} (l2 : Level) (M : Monoid l1) →
  (Normal-Submonoid (l1 ⊔ l2) M) retract-of (congruence-Monoid (l1 ⊔ l2) M)
pr1 (normal-submonoid-retract-of-congruence-Monoid l2 M) =
  congruence-Normal-Submonoid M
pr1 (pr2 (normal-submonoid-retract-of-congruence-Monoid l2 M)) =
  normal-submonoid-congruence-Monoid M
pr2 (pr2 (normal-submonoid-retract-of-congruence-Monoid l2 M)) =
  is-section-congruence-Normal-Submonoid l2 M
```

### The type of normal submonoids of `M` is equivalent to the type of saturated congruence relations on `M`

```agda
is-section-saturated-congruence-Normal-Submonoid :
  {l1 : Level} (l2 : Level) (M : Monoid l1) (N : Normal-Submonoid (l1 ⊔ l2) M) →
  ( normal-submonoid-saturated-congruence-Monoid M
    ( saturated-congruence-Normal-Submonoid M N)) ＝
  ( N)
is-section-saturated-congruence-Normal-Submonoid l2 M N =
  eq-has-same-elements-Normal-Submonoid M
    ( normal-submonoid-saturated-congruence-Monoid M
      ( saturated-congruence-Normal-Submonoid M N))
    ( N)
    ( has-same-elements-normal-submonoid-congruence-Normal-Submonoid M N)

is-retraction-saturated-congruence-Normal-Submonoid :
  {l1 : Level} (l2 : Level) (M : Monoid l1)
  (R : saturated-congruence-Monoid (l1 ⊔ l2) M) →
  ( saturated-congruence-Normal-Submonoid M
    ( normal-submonoid-saturated-congruence-Monoid M R)) ＝
  ( R)
is-retraction-saturated-congruence-Normal-Submonoid l2 M R =
  eq-relate-same-elements-saturated-congruence-Monoid M
    ( saturated-congruence-Normal-Submonoid M
      ( normal-submonoid-saturated-congruence-Monoid M R))
    ( R)
    ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Monoid
      ( M)
      ( R))

is-equiv-normal-submonoid-saturated-congruence-Monoid :
  {l1 : Level} (l2 : Level) (M : Monoid l1) →
  is-equiv (normal-submonoid-saturated-congruence-Monoid {l2 = l1 ⊔ l2} M)
is-equiv-normal-submonoid-saturated-congruence-Monoid l2 M =
  is-equiv-is-invertible
    ( saturated-congruence-Normal-Submonoid M)
    ( is-section-saturated-congruence-Normal-Submonoid l2 M)
    ( is-retraction-saturated-congruence-Normal-Submonoid l2 M)

equiv-normal-submonoid-saturated-congruence-Monoid :
  {l1 : Level} (l2 : Level) (M : Monoid l1) →
  saturated-congruence-Monoid (l1 ⊔ l2) M ≃ Normal-Submonoid (l1 ⊔ l2) M
pr1 (equiv-normal-submonoid-saturated-congruence-Monoid l2 M) =
  normal-submonoid-saturated-congruence-Monoid M
pr2 (equiv-normal-submonoid-saturated-congruence-Monoid l2 M) =
  is-equiv-normal-submonoid-saturated-congruence-Monoid l2 M
```

## References

- S. Margolis and J.-É. Pin, Inverse semigroups and extensions of groups by
  semilattices, J. of Algebra 110 (1987), 277-297.
