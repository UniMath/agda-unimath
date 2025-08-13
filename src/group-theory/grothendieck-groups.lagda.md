# Grothendieck groups

```agda
module group-theory.grothendieck-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-functoriality-set-quotients
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.existential-quantification
open import foundation.functoriality-set-quotients
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.set-quotients
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.cartesian-products-commutative-monoids
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import logic.functoriality-existential-quantification
```

</details>

## Idea

The
{{#concept "Grothendieck group" Disambiguation="associated to a commutative monoid" WD="Grothendieck group" WDID=Q1128678 Agda=grothendieck-ab-Commutative-Monoid}}, or **group of differences**,
of a [commutative monoid](group-theory.commutative-monoids.md) `M` is a certain
[abelian group](group-theory.abelian-groups.md) `K` such that for any
[commutative monoid homomorphism](group-theory.homomorphisms-commutative-monoids.md)
`f` from `M` to an abelian group `G`,
`f = g ∘ hom-grothendieck-ab-Commutative-Monoid M` for some unique `g`, an
[abelian group homomorphism](group-theory.homomorphisms-abelian-groups.md) from
`K` to `A`.

The Grothendieck group can be constructed as a
[quotient](foundation.set-quotients.md) of the
[product monoid](group-theory.cartesian-products-commutative-monoids.md) of `M`
with itself by the [equivalence relation](foundation.equivalence-relations.md)

```text
  (p₁ , n₁) ~ (p₂ , n₂) := ∃ (k : M) (p₁ * n₂ * k ＝ p₂ * n₁ * k)
```

Intuitively, `p` represents the "positive component" and `n` the "negative
component," but because one cannot necessarily cancel out multiplications in
monoids, the extra term `k` is needed.

## Definition

### The Grothendieck equivalence relation

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  (let _*_ = mul-Commutative-Monoid M)
  where

  grothendieck-relation-prop-Commutative-Monoid :
    Relation-Prop l (type-product-Commutative-Monoid M M)
  grothendieck-relation-prop-Commutative-Monoid (p1 , n1) (p2 , n2) =
    ∃ ( type-Commutative-Monoid M)
      ( λ k →
        Id-Prop
          ( set-Commutative-Monoid M)
          ( (p1 * n2) * k)
          ( (p2 * n1) * k))

  grothendieck-relation-Commutative-Monoid :
    Relation l (type-product-Commutative-Monoid M M)
  grothendieck-relation-Commutative-Monoid =
    type-Relation-Prop grothendieck-relation-prop-Commutative-Monoid

  refl-grothendieck-relation-Commutative-Monoid :
    is-reflexive-Relation-Prop grothendieck-relation-prop-Commutative-Monoid
  refl-grothendieck-relation-Commutative-Monoid _ =
    intro-exists (unit-Commutative-Monoid M) refl

  symmetric-grothendieck-relation-Commutative-Monoid :
    is-symmetric-Relation-Prop grothendieck-relation-prop-Commutative-Monoid
  symmetric-grothendieck-relation-Commutative-Monoid _ _ =
    map-tot-exists (λ _ → inv)

  abstract
    transitive-grothendieck-relation-Commutative-Monoid :
      is-transitive-Relation-Prop grothendieck-relation-prop-Commutative-Monoid
    transitive-grothendieck-relation-Commutative-Monoid
      (p1 , n1) (p2 , n2) (p3 , n3) ∃k23 ∃k12 =
        let
          open
            do-syntax-trunc-Prop
              ( grothendieck-relation-prop-Commutative-Monoid
                ( p1 , n1)
                ( p3 , n3))
          ap-* = ap-mul-Commutative-Monoid M
          interchange-*-* = interchange-mul-mul-Commutative-Monoid M
          assoc-* = associative-mul-Commutative-Monoid M
          comm-* = commutative-mul-Commutative-Monoid M
        in do
          (k23 , p2n3k23=p3n2k23) ← ∃k23
          (k12 , p1n2k12=p2n1k12) ← ∃k12
          intro-exists
            ((n2 * p2) * (k12 * k23))
            ( equational-reasoning
              (p1 * n3) * ((n2 * p2) * (k12 * k23))
              ＝ (p1 * n3) * ((n2 * k12) * (p2 * k23))
                by ap-* refl (interchange-*-* _ _ _ _)
              ＝ (p1 * (n2 * k12)) * (n3 * (p2 * k23))
                by interchange-*-* _ _ _ _
              ＝ (p1 * (n2 * k12)) * (p2 * (n3 * k23))
                by ap-* refl (left-swap-mul-Commutative-Monoid M _ _ _)
              ＝ ((p1 * n2) * k12) * ((p2 * n3) * k23)
                by inv (ap-* (assoc-* _ _ _) (assoc-* _ _ _))
              ＝ ((p2 * n1) * k12) * ((p3 * n2) * k23)
                by ap-* p1n2k12=p2n1k12 p2n3k23=p3n2k23
              ＝ ((p2 * n1) * (p3 * n2)) * (k12 * k23)
                by interchange-*-* _ _ _ _
              ＝ ((p3 * n2) * (p2 * n1)) * (k12 * k23)
                by ap-* (comm-* _ _) refl
              ＝ ((p3 * n2) * (n1 * p2)) * (k12 * k23)
                by ap-* (ap-* refl (comm-* _ _)) refl
              ＝ ((p3 * n1) * (n2 * p2)) * (k12 * k23)
                by ap-* (interchange-*-* _ _ _ _) refl
              ＝ (p3 * n1) * ((n2 * p2) * (k12 * k23))
                by assoc-* _ _ _)

    is-equivalence-relation-grothendieck-relation-prop-Commutative-Monoid :
      is-equivalence-relation grothendieck-relation-prop-Commutative-Monoid
    is-equivalence-relation-grothendieck-relation-prop-Commutative-Monoid =
      refl-grothendieck-relation-Commutative-Monoid ,
      symmetric-grothendieck-relation-Commutative-Monoid ,
      transitive-grothendieck-relation-Commutative-Monoid

  grothendieck-equivalence-relation-Commutative-Monoid :
    equivalence-relation
      ( l)
      ( type-product-Commutative-Monoid M M)
  grothendieck-equivalence-relation-Commutative-Monoid =
    grothendieck-relation-prop-Commutative-Monoid ,
    is-equivalence-relation-grothendieck-relation-prop-Commutative-Monoid
```

### The set quotient by the equivalence relation

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  set-grothendieck-ab-Commutative-Monoid : Set l
  set-grothendieck-ab-Commutative-Monoid =
    quotient-Set (grothendieck-equivalence-relation-Commutative-Monoid M)

  type-grothendieck-ab-Commutative-Monoid : UU l
  type-grothendieck-ab-Commutative-Monoid =
    set-quotient (grothendieck-equivalence-relation-Commutative-Monoid M)
```

### Addition in the Grothendieck group

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  (let _*_ = mul-Commutative-Monoid M)
  where

  abstract
    binary-hom-add-grothendieck-ab-Commutative-Monoid :
      binary-hom-equivalence-relation
        ( grothendieck-equivalence-relation-Commutative-Monoid M)
        ( grothendieck-equivalence-relation-Commutative-Monoid M)
        ( grothendieck-equivalence-relation-Commutative-Monoid M)
    pr1 binary-hom-add-grothendieck-ab-Commutative-Monoid
      (p1 , n1) (p2 , n2) = (p1 * p2 , n1 * n2)
    pr2 binary-hom-add-grothendieck-ab-Commutative-Monoid
      {p1 , n1} {p1' , n1'} {p2 , n2} {p2' , n2'} ∃k11' ∃k22' =
        let
          open
            do-syntax-trunc-Prop
              ( grothendieck-relation-prop-Commutative-Monoid
                ( M)
                ( p1 * p2 , n1 * n2)
                ( p1' * p2' , n1' * n2'))
          ap-* = ap-mul-Commutative-Monoid M
          interchange-*-* = interchange-mul-mul-Commutative-Monoid M
        in do
          (k11' , p1n1'k11'=p1'n1k11') ← ∃k11'
          (k22' , p2n2'k22'=p2'n2k22') ← ∃k22'
          intro-exists
            ( k11' * k22')
            ( equational-reasoning
              ((p1 * p2) * (n1' * n2')) * (k11' * k22')
              ＝ ((p1 * n1') * (p2 * n2')) * (k11' * k22')
                by ap-* (interchange-*-* _ _ _ _) refl
              ＝ ((p1 * n1') * k11') * ((p2 * n2') * k22')
                by interchange-*-* _ _ _ _
              ＝ ((p1' * n1) * k11') * ((p2' * n2) * k22')
                by ap-* p1n1'k11'=p1'n1k11' p2n2'k22'=p2'n2k22'
              ＝ ((p1' * n1) * (p2' * n2)) * (k11' * k22')
                by interchange-*-* _ _ _ _
              ＝ ((p1' * p2') * (n1 * n2)) * (k11' * k22')
                by ap-* (interchange-*-* _ _ _ _) refl)

  add-grothendieck-ab-Commutative-Monoid :
    type-grothendieck-ab-Commutative-Monoid M →
    type-grothendieck-ab-Commutative-Monoid M →
    type-grothendieck-ab-Commutative-Monoid M
  add-grothendieck-ab-Commutative-Monoid =
    binary-map-set-quotient
      ( grothendieck-equivalence-relation-Commutative-Monoid M)
      ( grothendieck-equivalence-relation-Commutative-Monoid M)
      ( grothendieck-equivalence-relation-Commutative-Monoid M)
      ( binary-hom-add-grothendieck-ab-Commutative-Monoid)

  add-grothendieck-ab-Commutative-Monoid' :
    type-grothendieck-ab-Commutative-Monoid M →
    type-grothendieck-ab-Commutative-Monoid M →
    type-grothendieck-ab-Commutative-Monoid M
  add-grothendieck-ab-Commutative-Monoid' x y =
    add-grothendieck-ab-Commutative-Monoid y x
```

### Mapping from the product monoid to the Grothendieck group

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  map-hom-grothendieck-ab-Commutative-Monoid' :
    type-product-Commutative-Monoid M M →
    type-grothendieck-ab-Commutative-Monoid M
  map-hom-grothendieck-ab-Commutative-Monoid' =
    quotient-map
      ( grothendieck-equivalence-relation-Commutative-Monoid M)
```

### The identity

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  unit-grothendieck-ab-Commutative-Monoid :
    type-grothendieck-ab-Commutative-Monoid M
  unit-grothendieck-ab-Commutative-Monoid =
    map-hom-grothendieck-ab-Commutative-Monoid' M
      ( unit-product-Commutative-Monoid M M)
```

### The map from the product monoid to the Grothendieck group turns multiplication to addition

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    compute-add-grothendieck-ab-Commutative-Monoid' :
      (x y : type-product-Commutative-Monoid M M) →
      add-grothendieck-ab-Commutative-Monoid M
        ( map-hom-grothendieck-ab-Commutative-Monoid' M x)
        ( map-hom-grothendieck-ab-Commutative-Monoid' M y) ＝
      map-hom-grothendieck-ab-Commutative-Monoid' M
        ( mul-product-Commutative-Monoid M M x y)
    compute-add-grothendieck-ab-Commutative-Monoid' =
      compute-binary-map-set-quotient
        ( grothendieck-equivalence-relation-Commutative-Monoid M)
        ( grothendieck-equivalence-relation-Commutative-Monoid M)
        ( grothendieck-equivalence-relation-Commutative-Monoid M)
        ( binary-hom-add-grothendieck-ab-Commutative-Monoid M)
```

### Commutativity of addition

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    commutative-add-grothendieck-ab-Commutative-Monoid :
      (x y : type-grothendieck-ab-Commutative-Monoid M) →
      add-grothendieck-ab-Commutative-Monoid M x y ＝
      add-grothendieck-ab-Commutative-Monoid M y x
    commutative-add-grothendieck-ab-Commutative-Monoid =
      double-induction-set-quotient'
        ( grothendieck-equivalence-relation-Commutative-Monoid M)
        ( λ x y →
          Id-Prop
            ( set-grothendieck-ab-Commutative-Monoid M)
            ( add-grothendieck-ab-Commutative-Monoid M x y)
            ( add-grothendieck-ab-Commutative-Monoid M y x))
        ( λ x y →
          compute-add-grothendieck-ab-Commutative-Monoid' M x y ∙
          ap
            ( map-hom-grothendieck-ab-Commutative-Monoid' M)
            ( commutative-mul-product-Commutative-Monoid M M x y) ∙
          inv (compute-add-grothendieck-ab-Commutative-Monoid' M y x))
```

### Unit laws for addition

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    left-unit-law-add-grothendieck-ab-Commutative-Monoid :
      (x : type-grothendieck-ab-Commutative-Monoid M) →
      add-grothendieck-ab-Commutative-Monoid M
        ( unit-grothendieck-ab-Commutative-Monoid M)
        x ＝
      x
    left-unit-law-add-grothendieck-ab-Commutative-Monoid =
      induction-set-quotient
        ( grothendieck-equivalence-relation-Commutative-Monoid M)
        ( λ x →
          Id-Prop
            ( set-grothendieck-ab-Commutative-Monoid M)
            ( add-grothendieck-ab-Commutative-Monoid M
              ( unit-grothendieck-ab-Commutative-Monoid M)
              ( x))
            ( x))
        ( λ x →
          compute-add-grothendieck-ab-Commutative-Monoid' M
            ( unit-product-Commutative-Monoid M M)
            ( x) ∙
          ap
            ( map-hom-grothendieck-ab-Commutative-Monoid' M)
            ( left-unit-law-mul-Commutative-Monoid
              ( product-Commutative-Monoid M M)
              ( x)))

    right-unit-law-add-grothendieck-ab-Commutative-Monoid :
      (x : type-grothendieck-ab-Commutative-Monoid M) →
      add-grothendieck-ab-Commutative-Monoid M
        ( x)
        ( unit-grothendieck-ab-Commutative-Monoid M) ＝
      x
    right-unit-law-add-grothendieck-ab-Commutative-Monoid _ =
      commutative-add-grothendieck-ab-Commutative-Monoid M _ _ ∙
      left-unit-law-add-grothendieck-ab-Commutative-Monoid _
```

### Associativity of addition

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    associative-add-grothendieck-ab-Commutative-Monoid :
      (x y z : type-grothendieck-ab-Commutative-Monoid M) →
      add-grothendieck-ab-Commutative-Monoid M
        ( add-grothendieck-ab-Commutative-Monoid M x y)
        ( z) ＝
      add-grothendieck-ab-Commutative-Monoid M
        ( x)
        ( add-grothendieck-ab-Commutative-Monoid M y z)
    associative-add-grothendieck-ab-Commutative-Monoid =
      triple-induction-set-quotient'
        ( grothendieck-equivalence-relation-Commutative-Monoid M)
        ( λ x y z →
          Id-Prop
            ( set-grothendieck-ab-Commutative-Monoid M)
            ( add-grothendieck-ab-Commutative-Monoid M
              ( add-grothendieck-ab-Commutative-Monoid M x y)
              ( z))
            ( add-grothendieck-ab-Commutative-Monoid M
              ( x)
              ( add-grothendieck-ab-Commutative-Monoid M y z)))
        ( λ x y z →
          ap
            ( add-grothendieck-ab-Commutative-Monoid' M
              ( map-hom-grothendieck-ab-Commutative-Monoid' M z))
            ( compute-add-grothendieck-ab-Commutative-Monoid' M x y) ∙
          compute-add-grothendieck-ab-Commutative-Monoid' M
            ( mul-product-Commutative-Monoid M M x y)
            ( z) ∙
          ap
            ( map-hom-grothendieck-ab-Commutative-Monoid' M)
            ( associative-mul-product-Commutative-Monoid M M x y z) ∙
          inv
            ( compute-add-grothendieck-ab-Commutative-Monoid' M
              ( x)
              ( mul-product-Commutative-Monoid M M y z)) ∙
          ap
            ( add-grothendieck-ab-Commutative-Monoid M
              ( map-hom-grothendieck-ab-Commutative-Monoid' M x))
            ( inv (compute-add-grothendieck-ab-Commutative-Monoid' M y z)))
```

### The commutative monoid of Grothendieck addition

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  semigroup-grothendieck-ab-Commutative-Monoid : Semigroup l
  semigroup-grothendieck-ab-Commutative-Monoid =
    ( set-grothendieck-ab-Commutative-Monoid M ,
      add-grothendieck-ab-Commutative-Monoid M ,
      associative-add-grothendieck-ab-Commutative-Monoid M)

  monoid-grothendieck-ab-Commutative-Monoid : Monoid l
  monoid-grothendieck-ab-Commutative-Monoid =
    ( semigroup-grothendieck-ab-Commutative-Monoid ,
      unit-grothendieck-ab-Commutative-Monoid M ,
      left-unit-law-add-grothendieck-ab-Commutative-Monoid M ,
      right-unit-law-add-grothendieck-ab-Commutative-Monoid M)

  commutative-monoid-grothendieck-ab-Commutative-Monoid :
    Commutative-Monoid l
  commutative-monoid-grothendieck-ab-Commutative-Monoid =
    ( monoid-grothendieck-ab-Commutative-Monoid ,
      commutative-add-grothendieck-ab-Commutative-Monoid M)
```

### The monoid homomorphism from the original monoid to the commutative monoid of Grothendieck addition

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  hom-grothendieck-ab-Commutative-Monoid' :
    hom-Commutative-Monoid
      ( product-Commutative-Monoid M M)
      ( commutative-monoid-grothendieck-ab-Commutative-Monoid M)
  hom-grothendieck-ab-Commutative-Monoid' =
    ( map-hom-grothendieck-ab-Commutative-Monoid' M ,
      inv (compute-add-grothendieck-ab-Commutative-Monoid' M _ _)) ,
    refl

  hom-grothendieck-ab-Commutative-Monoid :
    hom-Commutative-Monoid
      ( M)
      ( commutative-monoid-grothendieck-ab-Commutative-Monoid M)
  hom-grothendieck-ab-Commutative-Monoid =
    comp-hom-Commutative-Monoid
      ( M)
      ( product-Commutative-Monoid M M)
      ( commutative-monoid-grothendieck-ab-Commutative-Monoid M)
      ( hom-grothendieck-ab-Commutative-Monoid')
      ( left-hom-product-Commutative-Monoid M M)

  map-hom-grothendieck-ab-Commutative-Monoid :
    type-Commutative-Monoid M →
    type-grothendieck-ab-Commutative-Monoid M
  map-hom-grothendieck-ab-Commutative-Monoid =
    map-hom-Commutative-Monoid
      ( M)
      ( commutative-monoid-grothendieck-ab-Commutative-Monoid M)
      ( hom-grothendieck-ab-Commutative-Monoid)
```

### The negation operation

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  (let _*_ = mul-Commutative-Monoid M)
  where

  inv-product-grothendieck-ab-Commutative-Monoid :
    type-product-Commutative-Monoid M M →
    type-product-Commutative-Monoid M M
  inv-product-grothendieck-ab-Commutative-Monoid (p , n) = (n , p)

  hom-inv-grothendieck-ab-Commutative-Monoid' :
    hom-equivalence-relation
      ( grothendieck-equivalence-relation-Commutative-Monoid M)
      ( grothendieck-equivalence-relation-Commutative-Monoid M)
  pr1 hom-inv-grothendieck-ab-Commutative-Monoid' =
    inv-product-grothendieck-ab-Commutative-Monoid
  pr2 hom-inv-grothendieck-ab-Commutative-Monoid'
    {p , n} {p' , n'} ∃k =
      let
        open
          do-syntax-trunc-Prop
            ( grothendieck-relation-prop-Commutative-Monoid M
              ( n , p)
              ( n' , p'))
        ap-* = ap-mul-Commutative-Monoid M
        comm-* = commutative-mul-Commutative-Monoid M
      in do
        (k , pn'k=p'nk) ← ∃k
        intro-exists
          ( k)
          ( equational-reasoning
            (n * p') * k
            ＝ (p' * n) * k by ap-* (comm-* _ _) refl
            ＝ (p * n') * k by inv pn'k=p'nk
            ＝ (n' * p) * k by ap-* (comm-* _ _) refl)

  inv-grothendieck-ab-Commutative-Monoid :
    type-grothendieck-ab-Commutative-Monoid M →
    type-grothendieck-ab-Commutative-Monoid M
  inv-grothendieck-ab-Commutative-Monoid =
    map-set-quotient
      ( grothendieck-equivalence-relation-Commutative-Monoid M)
      ( grothendieck-equivalence-relation-Commutative-Monoid M)
      ( hom-inv-grothendieck-ab-Commutative-Monoid')

  abstract
    compute-inv-grothendieck-ab-Commutative-Monoid' :
      (x : type-product-Commutative-Monoid M M) →
      inv-grothendieck-ab-Commutative-Monoid
        ( map-hom-grothendieck-ab-Commutative-Monoid' M x) ＝
      map-hom-grothendieck-ab-Commutative-Monoid' M
        ( inv-product-grothendieck-ab-Commutative-Monoid x)
    compute-inv-grothendieck-ab-Commutative-Monoid' =
      coherence-square-map-set-quotient
        ( grothendieck-equivalence-relation-Commutative-Monoid M)
        ( grothendieck-equivalence-relation-Commutative-Monoid M)
        ( hom-inv-grothendieck-ab-Commutative-Monoid')
```

### Inverse laws of addition

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  (let _*_ = mul-Commutative-Monoid M)
  where

  abstract
    left-inverse-law-product-grothendieck-ab-Commutative-Monoid :
      ( x : type-product-Commutative-Monoid M M) →
      grothendieck-relation-Commutative-Monoid M
        ( mul-product-Commutative-Monoid M M
          ( inv-product-grothendieck-ab-Commutative-Monoid M x)
          ( x))
        ( unit-product-Commutative-Monoid M M)
    left-inverse-law-product-grothendieck-ab-Commutative-Monoid (p , n) =
      let
        comm-* = commutative-mul-Commutative-Monoid M
        u = unit-Commutative-Monoid M
      in
        intro-exists
          ( u)
          ( ap (_* u) (comm-* _ _ ∙ ap (u *_) (comm-* _ _)))

    left-inverse-law-add-grothendieck-ab-Commutative-Monoid :
      (x : type-grothendieck-ab-Commutative-Monoid M) →
      add-grothendieck-ab-Commutative-Monoid M
        ( inv-grothendieck-ab-Commutative-Monoid M x)
        ( x) ＝
      unit-grothendieck-ab-Commutative-Monoid M
    left-inverse-law-add-grothendieck-ab-Commutative-Monoid =
      induction-set-quotient
        ( grothendieck-equivalence-relation-Commutative-Monoid M)
        ( λ x →
          Id-Prop
            ( set-grothendieck-ab-Commutative-Monoid M)
            ( add-grothendieck-ab-Commutative-Monoid M
              ( inv-grothendieck-ab-Commutative-Monoid M x)
              ( x))
            ( unit-grothendieck-ab-Commutative-Monoid M))
        ( λ x →
          ap
            ( add-grothendieck-ab-Commutative-Monoid' M
              ( map-hom-grothendieck-ab-Commutative-Monoid' M x))
            ( compute-inv-grothendieck-ab-Commutative-Monoid' M x) ∙
          compute-add-grothendieck-ab-Commutative-Monoid' M _ _ ∙
          apply-effectiveness-quotient-map'
            ( grothendieck-equivalence-relation-Commutative-Monoid M)
            ( left-inverse-law-product-grothendieck-ab-Commutative-Monoid
              ( x)))

    right-inverse-law-add-grothendieck-ab-Commutative-Monoid :
      (x : type-grothendieck-ab-Commutative-Monoid M) →
      add-grothendieck-ab-Commutative-Monoid M
        ( x)
        ( inv-grothendieck-ab-Commutative-Monoid M x) ＝
      unit-grothendieck-ab-Commutative-Monoid M
    right-inverse-law-add-grothendieck-ab-Commutative-Monoid x =
      commutative-add-grothendieck-ab-Commutative-Monoid M _ _ ∙
      left-inverse-law-add-grothendieck-ab-Commutative-Monoid x
```

### The Grothendieck group

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  group-grothendieck-ab-Commutative-Monoid : Group l
  group-grothendieck-ab-Commutative-Monoid =
    ( semigroup-grothendieck-ab-Commutative-Monoid M ,
      ( unit-grothendieck-ab-Commutative-Monoid M ,
        left-unit-law-add-grothendieck-ab-Commutative-Monoid M ,
        right-unit-law-add-grothendieck-ab-Commutative-Monoid M) ,
      inv-grothendieck-ab-Commutative-Monoid M ,
      left-inverse-law-add-grothendieck-ab-Commutative-Monoid M ,
      right-inverse-law-add-grothendieck-ab-Commutative-Monoid M)

  grothendieck-ab-Commutative-Monoid : Ab l
  grothendieck-ab-Commutative-Monoid =
    ( group-grothendieck-ab-Commutative-Monoid ,
      commutative-add-grothendieck-ab-Commutative-Monoid M)

  abstract
    compute-add-grothendieck-ab-Commutative-Monoid :
      (x y : type-Commutative-Monoid M) →
      add-grothendieck-ab-Commutative-Monoid M
        ( map-hom-grothendieck-ab-Commutative-Monoid M x)
        ( map-hom-grothendieck-ab-Commutative-Monoid M y) ＝
      map-hom-grothendieck-ab-Commutative-Monoid M
        ( mul-Commutative-Monoid M x y)
    compute-add-grothendieck-ab-Commutative-Monoid x y =
      inv
        ( preserves-mul-hom-Commutative-Monoid
          ( M)
          ( commutative-monoid-grothendieck-ab-Commutative-Monoid M)
          ( hom-grothendieck-ab-Commutative-Monoid M))
```

## Properties

### The universal property of the Grothendieck group

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (G : Ab l2)
  (let MG = commutative-monoid-Ab G)
  (f : hom-Commutative-Monoid M MG)
  where

  map-untruncated-universal-property-grothendieck-ab-Commutative-Monoid :
    type-product-Commutative-Monoid M M → type-Ab G
  map-untruncated-universal-property-grothendieck-ab-Commutative-Monoid
    (p , n) =
    add-Ab G
      ( map-hom-Commutative-Monoid M MG f p)
      ( neg-Ab G (map-hom-Commutative-Monoid M MG f n))

  hom-map-untruncated-universal-property-grothendieck-ab-Commutative-Monoid :
    hom-equivalence-relation
      ( grothendieck-equivalence-relation-Commutative-Monoid M)
      ( Id-equivalence-relation (set-Ab G))
  pr1
    hom-map-untruncated-universal-property-grothendieck-ab-Commutative-Monoid =
      map-untruncated-universal-property-grothendieck-ab-Commutative-Monoid
  pr2
    hom-map-untruncated-universal-property-grothendieck-ab-Commutative-Monoid
      {p1 , n1} {p2 , n2} ∃k =
        let
          open
            do-syntax-trunc-Prop
              ( Id-Prop
                ( set-Ab G)
                ( map-untruncated-universal-property-grothendieck-ab-Commutative-Monoid
                  (p1 , n1))
                ( map-untruncated-universal-property-grothendieck-ab-Commutative-Monoid
                  (p2 , n2)))
        in do
          (k , p1n2k=p2n1k) ← ∃k
          equational-reasoning
            add-Ab G
              ( map-hom-Commutative-Monoid M MG f p1)
              ( neg-Ab G (map-hom-Commutative-Monoid M MG f n1))
            ＝
              add-Ab G
                ( add-Ab G
                  ( map-hom-Commutative-Monoid M MG f p1)
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f n1)))
                ( zero-Ab G)
              by inv (right-unit-law-add-Ab G _)
            ＝
              add-Ab G
                ( add-Ab G
                  ( map-hom-Commutative-Monoid M MG f p1)
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f n1)))
                ( add-Ab G
                  ( map-hom-Commutative-Monoid M MG f n2)
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f n2)))
              by
                ap-add-Ab G refl (inv (right-inverse-law-add-Ab G _))
            ＝
              add-Ab G
                ( add-Ab G
                  ( map-hom-Commutative-Monoid M MG f p1)
                  ( map-hom-Commutative-Monoid M MG f n2))
                ( add-Ab G
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f n1))
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f n2)))
              by interchange-add-add-Ab G _ _ _ _
            ＝
              add-Ab G
                ( add-Ab G
                  ( add-Ab G
                    ( map-hom-Commutative-Monoid M MG f p1)
                    ( map-hom-Commutative-Monoid M MG f n2))
                  ( add-Ab G
                    ( neg-Ab G (map-hom-Commutative-Monoid M MG f n1))
                    ( neg-Ab G (map-hom-Commutative-Monoid M MG f n2))))
                ( zero-Ab G)
              by inv (right-unit-law-add-Ab G _)
            ＝
              add-Ab G
                ( add-Ab G
                  ( map-hom-Commutative-Monoid M MG f
                    ( mul-Commutative-Monoid M p1 n2))
                  ( add-Ab G
                    ( neg-Ab G (map-hom-Commutative-Monoid M MG f n1))
                    ( neg-Ab G (map-hom-Commutative-Monoid M MG f n2))))
                ( add-Ab G
                  ( map-hom-Commutative-Monoid M MG f k)
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f k)))
              by
                inv
                  ( ap-add-Ab G
                    ( ap-add-Ab G
                      ( preserves-mul-hom-Commutative-Monoid M MG f)
                      ( refl))
                    ( right-inverse-law-add-Ab G _))
            ＝
              add-Ab G
                ( add-Ab G
                  ( map-hom-Commutative-Monoid M MG f
                    ( mul-Commutative-Monoid M p1 n2))
                  ( map-hom-Commutative-Monoid M MG f k))
                ( add-Ab G
                  ( add-Ab G
                    ( neg-Ab G (map-hom-Commutative-Monoid M MG f n1))
                    ( neg-Ab G (map-hom-Commutative-Monoid M MG f n2)))
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f k)))
              by interchange-add-add-Ab G _ _ _ _
            ＝
              add-Ab G
                ( map-hom-Commutative-Monoid M MG f
                  ( mul-Commutative-Monoid M
                    ( mul-Commutative-Monoid M p1 n2)
                    ( k)))
                ( add-Ab G
                  ( add-Ab G
                    ( neg-Ab G (map-hom-Commutative-Monoid M MG f n1))
                    ( neg-Ab G (map-hom-Commutative-Monoid M MG f n2)))
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f k)))
              by
                ap-add-Ab G
                  ( inv (preserves-mul-hom-Commutative-Monoid M MG f))
                  ( refl)
            ＝
              add-Ab G
                ( map-hom-Commutative-Monoid M MG f
                  ( mul-Commutative-Monoid M
                    ( mul-Commutative-Monoid M p2 n1)
                    ( k)))
                ( add-Ab G
                  ( add-Ab G
                    ( neg-Ab G (map-hom-Commutative-Monoid M MG f n1))
                    ( neg-Ab G (map-hom-Commutative-Monoid M MG f n2)))
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f k)))
              by
                ap-add-Ab G
                  ( ap (map-hom-Commutative-Monoid M MG f) p1n2k=p2n1k)
                  ( refl)
            ＝
              add-Ab G
                ( add-Ab G
                  ( map-hom-Commutative-Monoid M MG f
                    ( mul-Commutative-Monoid M p2 n1))
                  ( map-hom-Commutative-Monoid M MG f k))
                ( add-Ab G
                  ( add-Ab G
                    ( neg-Ab G (map-hom-Commutative-Monoid M MG f n1))
                    ( neg-Ab G (map-hom-Commutative-Monoid M MG f n2)))
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f k)))
              by ap-add-Ab G (preserves-mul-hom-Commutative-Monoid M MG f) refl
            ＝
              add-Ab G
                ( add-Ab G
                  ( map-hom-Commutative-Monoid M MG f
                    ( mul-Commutative-Monoid M p2 n1))
                  ( add-Ab G
                    ( neg-Ab G (map-hom-Commutative-Monoid M MG f n1))
                    ( neg-Ab G (map-hom-Commutative-Monoid M MG f n2))))
                ( add-Ab G
                  ( map-hom-Commutative-Monoid M MG f k)
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f k)))
              by interchange-add-add-Ab G _ _ _ _
            ＝
              add-Ab G
                ( add-Ab G
                  ( add-Ab G
                    ( map-hom-Commutative-Monoid M MG f p2)
                    ( map-hom-Commutative-Monoid M MG f n1))
                  ( add-Ab G
                    ( neg-Ab G (map-hom-Commutative-Monoid M MG f n1))
                    ( neg-Ab G (map-hom-Commutative-Monoid M MG f n2))))
                ( zero-Ab G)
              by
                ap-add-Ab G
                  ( ap-add-Ab G
                    ( preserves-mul-hom-Commutative-Monoid M MG f)
                    ( refl))
                  ( right-inverse-law-add-Ab G _)
            ＝
              add-Ab G
                ( add-Ab G
                  ( map-hom-Commutative-Monoid M MG f p2)
                  ( map-hom-Commutative-Monoid M MG f n1))
                ( add-Ab G
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f n1))
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f n2)))
              by right-unit-law-add-Ab G _
            ＝
              add-Ab G
                ( add-Ab G
                  ( map-hom-Commutative-Monoid M MG f n1)
                  ( map-hom-Commutative-Monoid M MG f p2))
                ( add-Ab G
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f n1))
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f n2)))
              by ap-add-Ab G (commutative-add-Ab G _ _) refl
            ＝
              add-Ab G
                ( add-Ab G
                  ( map-hom-Commutative-Monoid M MG f n1)
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f n1)))
                ( add-Ab G
                  ( map-hom-Commutative-Monoid M MG f p2)
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f n2)))
              by interchange-add-add-Ab G _ _ _ _
            ＝
              add-Ab G
                ( zero-Ab G)
                ( add-Ab G
                  ( map-hom-Commutative-Monoid M MG f p2)
                  ( neg-Ab G (map-hom-Commutative-Monoid M MG f n2)))
              by ap-add-Ab G (right-inverse-law-add-Ab G _) refl
            ＝
              add-Ab G
                ( map-hom-Commutative-Monoid M MG f p2)
                ( neg-Ab G (map-hom-Commutative-Monoid M MG f n2))
              by left-unit-law-add-Ab G _

  map-hom-universal-property-grothendieck-ab-Commutative-Monoid :
    type-grothendieck-ab-Commutative-Monoid M → type-Ab G
  map-hom-universal-property-grothendieck-ab-Commutative-Monoid =
    map-is-set-quotient
      ( grothendieck-equivalence-relation-Commutative-Monoid M)
      ( set-grothendieck-ab-Commutative-Monoid M)
      ( reflecting-map-quotient-map
        ( grothendieck-equivalence-relation-Commutative-Monoid M))
      ( Id-equivalence-relation (set-Ab G))
      ( set-Ab G)
      ( id-reflecting-map-Id-equivalence-relation (set-Ab G))
      ( is-set-quotient-set-quotient
        ( grothendieck-equivalence-relation-Commutative-Monoid M))
      ( is-set-quotient-id-Id-equivalence-relation (set-Ab G))
      ( hom-map-untruncated-universal-property-grothendieck-ab-Commutative-Monoid)
```

We have yet to prove that this is a group homomorphism or that it is unique.

## External links

- [Grothendieck group](https://en.wikipedia.org/wiki/Grothendieck_group) on Wikipedia
- [Grothendieck group](https://ncatlab.org/nlab/show/Grothendieck+group) on $n$Lab
- [Grothendieck group](https://encyclopediaofmath.org/wiki/Grothendieck_group) on Encyclopedia of Mathematics
