# Equivalence relations

```agda
module foundation.equivalence-relations where

open import foundation-core.equivalence-relations public
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.fundamental-theorem-of-equivalence-relations
open import foundation.logical-equivalences
open import foundation.partitions
open import foundation.propositional-truncations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sigma-decompositions
open import foundation.surjective-maps
open import foundation.uniqueness-set-quotients
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Properties

### Equivalence relations are equivalent to set-indexed Σ-decompositions

#### The Σ-decomposition obtained from an equivalence relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  set-indexed-Σ-decomposition-equivalence-relation :
    Set-Indexed-Σ-Decomposition (l1 ⊔ l2) (l1 ⊔ l2) A
  set-indexed-Σ-decomposition-equivalence-relation =
    set-indexed-Σ-decomposition-partition (partition-equivalence-relation R)
```

### The type of equivalence relations on `A` is equivalent to the type of sets `X` equipped with a surjective map from `A` into `X`

#### The surjection into a set obtained from an equivalence relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  surjection-into-set-equivalence-relation :
    Surjection-Into-Set (l1 ⊔ l2) A
  pr1 surjection-into-set-equivalence-relation = quotient-Set R
  pr2 surjection-into-set-equivalence-relation = surjection-quotient-map R
```

#### The equivalence relation obtained from a surjection into a set

```agda
module _
  {l1 l2 : Level} {A : UU l1} (X : Set l2) (f : A → type-Set X)
  where

  rel-map-into-set : Relation-Prop l2 A
  rel-map-into-set x y = Id-Prop X (f x) (f y)

  sim-map-into-set : Relation l2 A
  sim-map-into-set x y = type-Prop (rel-map-into-set x y)

  refl-sim-map-into-set : is-reflexive sim-map-into-set
  refl-sim-map-into-set x = refl

  symmetric-sim-map-into-set : is-symmetric sim-map-into-set
  symmetric-sim-map-into-set x y H = inv H

  transitive-sim-map-into-set : is-transitive sim-map-into-set
  transitive-sim-map-into-set x y z H K = K ∙ H

  equivalence-relation-map-into-set : equivalence-relation l2 A
  pr1 equivalence-relation-map-into-set = rel-map-into-set
  pr1 (pr2 equivalence-relation-map-into-set) x = refl-sim-map-into-set x
  pr1 (pr2 (pr2 equivalence-relation-map-into-set)) x y =
    symmetric-sim-map-into-set x y
  pr2 (pr2 (pr2 equivalence-relation-map-into-set)) x y z =
    transitive-sim-map-into-set x y z

  is-effective-map-into-set :
    is-effective equivalence-relation-map-into-set f
  is-effective-map-into-set x y = id-equiv

equivalence-relation-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} →
  Surjection-Into-Set l2 A → equivalence-relation l2 A
equivalence-relation-Surjection-Into-Set f =
  equivalence-relation-map-into-set
    ( set-Surjection-Into-Set f)
    ( map-Surjection-Into-Set f)

is-effective-map-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  is-effective
    ( equivalence-relation-Surjection-Into-Set f)
    ( map-Surjection-Into-Set f)
is-effective-map-Surjection-Into-Set f =
  is-effective-map-into-set
    ( set-Surjection-Into-Set f)
    ( map-Surjection-Into-Set f)
```

#### The equivalence relation obtained from the quotient map induced by an equivalence relation is that same equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  relate-same-elements-equivalence-relation-surjection-into-set-equivalence-relation :
    relate-same-elements-equivalence-relation
      ( equivalence-relation-Surjection-Into-Set
        ( surjection-into-set-equivalence-relation R))
      ( R)
  relate-same-elements-equivalence-relation-surjection-into-set-equivalence-relation
    x y =
    iff-equiv (is-effective-quotient-map R x y)

is-retraction-equivalence-relation-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation (l1 ⊔ l2) A) →
  equivalence-relation-Surjection-Into-Set
    ( surjection-into-set-equivalence-relation R) ＝
  R
is-retraction-equivalence-relation-Surjection-Into-Set R =
  eq-relate-same-elements-equivalence-relation
    ( equivalence-relation-Surjection-Into-Set
      ( surjection-into-set-equivalence-relation R))
    ( R)
    ( relate-same-elements-equivalence-relation-surjection-into-set-equivalence-relation
      R)
```

#### The surjection into a set obtained from the equivalence relation induced by a surjection into a set is the original surjection into a set

```agda
equiv-surjection-into-set-equivalence-relation-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  equiv-Surjection-Into-Set
    ( surjection-into-set-equivalence-relation
      ( equivalence-relation-Surjection-Into-Set f))
    ( f)
equiv-surjection-into-set-equivalence-relation-Surjection-Into-Set f =
  center
    ( uniqueness-set-quotient
      ( equivalence-relation-Surjection-Into-Set f)
      ( quotient-Set (equivalence-relation-Surjection-Into-Set f))
      ( reflecting-map-quotient-map
        ( equivalence-relation-Surjection-Into-Set f))
      ( is-set-quotient-set-quotient
        ( equivalence-relation-Surjection-Into-Set f))
      ( set-Surjection-Into-Set f)
      ( pair
        ( map-Surjection-Into-Set f)
        ( λ H → H))
      ( is-set-quotient-is-surjective-and-effective
        ( equivalence-relation-Surjection-Into-Set f)
        ( set-Surjection-Into-Set f)
        ( pr1 (pr2 f) , (λ {x} {y} z → z))
        ( pair
          ( is-surjective-Surjection-Into-Set f)
          ( is-effective-map-Surjection-Into-Set f))))

is-section-equivalence-relation-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set (l1 ⊔ l2) A) →
  surjection-into-set-equivalence-relation
    ( equivalence-relation-Surjection-Into-Set f) ＝
  f
is-section-equivalence-relation-Surjection-Into-Set f =
  eq-equiv-Surjection-Into-Set
    ( surjection-into-set-equivalence-relation
      ( equivalence-relation-Surjection-Into-Set f))
    ( f)
    ( equiv-surjection-into-set-equivalence-relation-Surjection-Into-Set f)
```

#### The type of equivalence relations on `A` is equivalent to the type of surjections from `A` into a set

```agda
is-equiv-surjection-into-set-equivalence-relation :
  {l1 : Level} {A : UU l1} →
  is-equiv (surjection-into-set-equivalence-relation {l1} {l1} {A})
is-equiv-surjection-into-set-equivalence-relation {l1} {A} =
  is-equiv-is-invertible
    ( equivalence-relation-Surjection-Into-Set {l1} {l1} {A})
    ( is-section-equivalence-relation-Surjection-Into-Set {l1} {l1} {A})
    ( is-retraction-equivalence-relation-Surjection-Into-Set {l1} {l1} {A})

equiv-surjection-into-set-equivalence-relation :
  {l1 : Level} (A : UU l1) →
  equivalence-relation l1 A ≃ Surjection-Into-Set l1 A
pr1 (equiv-surjection-into-set-equivalence-relation A) =
  surjection-into-set-equivalence-relation
pr2 (equiv-surjection-into-set-equivalence-relation A) =
  is-equiv-surjection-into-set-equivalence-relation
```

### Equality on a set is an equivalence relation

```agda
module _
  {l1 : Level} (A : Set l1)
  where

  Id-equivalence-relation : equivalence-relation l1 (type-Set A)
  pr1 Id-equivalence-relation = Id-Prop A
  pr1 (pr2 Id-equivalence-relation) _ = refl
  pr1 (pr2 (pr2 Id-equivalence-relation)) _ _ = inv
  pr2 (pr2 (pr2 Id-equivalence-relation)) _ _ _ H K = K ∙ H

  id-reflects-Id-equivalence-relation :
    reflects-equivalence-relation Id-equivalence-relation id
  id-reflects-Id-equivalence-relation = id

  id-reflecting-map-Id-equivalence-relation :
    reflecting-map-equivalence-relation Id-equivalence-relation (type-Set A)
  pr1 id-reflecting-map-Id-equivalence-relation = id
  pr2 id-reflecting-map-Id-equivalence-relation =
    id-reflects-Id-equivalence-relation

  is-surjective-and-effective-id-Id-equivalence-relation :
    is-surjective-and-effective Id-equivalence-relation id
  pr1 is-surjective-and-effective-id-Id-equivalence-relation a =
    unit-trunc-Prop (a , refl)
  pr2 is-surjective-and-effective-id-Id-equivalence-relation a b = id-equiv
```

### For any set `A`, `Id` is a set quotient for the equality relation

```agda
module _
  {l : Level} (A : Set l)
  where

  is-set-quotient-id-Id-equivalence-relation :
    is-set-quotient
      ( Id-equivalence-relation A)
      ( A)
      ( id-reflecting-map-Id-equivalence-relation A)
  is-set-quotient-id-Id-equivalence-relation =
    is-set-quotient-is-surjective-and-effective (Id-equivalence-relation A) A
      ( id-reflecting-map-Id-equivalence-relation A)
      ( is-surjective-and-effective-id-Id-equivalence-relation A)
```
