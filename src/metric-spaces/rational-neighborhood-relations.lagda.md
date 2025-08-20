# Rational neighborhood relations

```agda
module metric-spaces.rational-neighborhood-relations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "rational neighborhood relation" Agda=Rational-Neighborhood-Relation}}
is a type family of
[proposition-valued binary relations](foundation.binary-relations.md) indexed by
the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md).

Given a rational neighborhood relation `N` on `A` and some positive rational
number `d : ℚ⁺` such that `N d x y` holds for some pair of points `x y : A`, we
interpret `d` as an
{{#concept "upper bound" Disambiguation="on the distance with respect to a rational neighborhood relation" Agda=is-upper-bound-dist-Rational-Neighborhood-Relation}}
on the distance between `x` and `y` with respect to the rational neighborhood
relation.

## Definitions

### Rational neighborhood relations on a type

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  Rational-Neighborhood-Relation : UU (l1 ⊔ lsuc l2)
  Rational-Neighborhood-Relation = ℚ⁺ → Relation-Prop l2 A

module _
  {l1 l2 : Level} {A : UU l1} (B : Rational-Neighborhood-Relation l2 A)
  where

  neighborhood-Rational-Neighborhood-Relation :
    ℚ⁺ → Relation l2 A
  neighborhood-Rational-Neighborhood-Relation d x y =
    type-Prop (B d x y)

  is-prop-neighborhood-Rational-Neighborhood-Relation :
    (d : ℚ⁺) (x y : A) →
    is-prop (neighborhood-Rational-Neighborhood-Relation d x y)
  is-prop-neighborhood-Rational-Neighborhood-Relation d x y =
    is-prop-type-Prop (B d x y)

  is-upper-bound-dist-prop-Rational-Neighborhood-Relation :
    A → A → ℚ⁺ → Prop l2
  is-upper-bound-dist-prop-Rational-Neighborhood-Relation x y d = B d x y

  is-upper-bound-dist-Rational-Neighborhood-Relation :
    A → A → ℚ⁺ → UU l2
  is-upper-bound-dist-Rational-Neighborhood-Relation x y d =
    neighborhood-Rational-Neighborhood-Relation d x y

  is-prop-is-upper-bound-dist-Rational-Neighborhood-Relation :
    (x y : A) (d : ℚ⁺) →
    is-prop (is-upper-bound-dist-Rational-Neighborhood-Relation x y d)
  is-prop-is-upper-bound-dist-Rational-Neighborhood-Relation x y d =
    is-prop-neighborhood-Rational-Neighborhood-Relation d x y
```

## Properties

### Equality of rational neighborhood relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (N : Rational-Neighborhood-Relation l2 A)
  {l2' : Level} (N' : Rational-Neighborhood-Relation l2' A)
  where

  Eq-prop-Rational-Neighborhood-Relation : Prop (l1 ⊔ l2 ⊔ l2')
  Eq-prop-Rational-Neighborhood-Relation =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( A)
          ( λ x →
            Π-Prop
              ( A)
              ( λ y → N d x y ⇔ N' d x y)))

  Eq-Rational-Neighborhood-Relation : UU (l1 ⊔ l2 ⊔ l2')
  Eq-Rational-Neighborhood-Relation =
    type-Prop Eq-prop-Rational-Neighborhood-Relation

  is-prop-Eq-Rational-Neighborhood-Relation :
    is-prop Eq-Rational-Neighborhood-Relation
  is-prop-Eq-Rational-Neighborhood-Relation =
    is-prop-type-Prop Eq-prop-Rational-Neighborhood-Relation
```

### Identity principle for rational neighborhood relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (N : Rational-Neighborhood-Relation l2 A)
  where

  refl-Eq-Rational-Neighborhood-Relation : Eq-Rational-Neighborhood-Relation N N
  refl-Eq-Rational-Neighborhood-Relation d x y = id-iff

  Eq-eq-Rational-Neighborhood-Relation :
    (N' : Rational-Neighborhood-Relation l2 A) →
    N ＝ N' →
    Eq-Rational-Neighborhood-Relation N N'
  Eq-eq-Rational-Neighborhood-Relation .N refl =
    refl-Eq-Rational-Neighborhood-Relation

  eq-Eq-Rational-Neighborhood-Relation :
    (N' : Rational-Neighborhood-Relation l2 A) →
    Eq-Rational-Neighborhood-Relation N N' →
    N ＝ N'
  eq-Eq-Rational-Neighborhood-Relation N' H =
    eq-htpy
      ( λ d →
        eq-htpy
        ( λ x →
          eq-htpy
          ( λ y →
            eq-iff' (N d x y) (N' d x y) (H d x y))))

  abstract
    is-torsorial-Eq-Rational-Neighborhood-Relation :
      is-torsorial
        ( λ ( N' : Rational-Neighborhood-Relation l2 A) →
            ( Eq-Rational-Neighborhood-Relation N N'))
    is-torsorial-Eq-Rational-Neighborhood-Relation =
      ( N , refl-Eq-Rational-Neighborhood-Relation) ,
      ( λ (N' , e) →
        eq-type-subtype
          ( Eq-prop-Rational-Neighborhood-Relation N)
          ( eq-Eq-Rational-Neighborhood-Relation N' e))

  is-fiberwise-equiv-Eq-eq-Rational-Neighborhood-Relation :
    (N' : Rational-Neighborhood-Relation l2 A) →
    is-equiv (Eq-eq-Rational-Neighborhood-Relation N')
  is-fiberwise-equiv-Eq-eq-Rational-Neighborhood-Relation =
    fundamental-theorem-id
      is-torsorial-Eq-Rational-Neighborhood-Relation
      Eq-eq-Rational-Neighborhood-Relation

  equiv-Eq-eq-Rational-Neighborhood-Relation :
    (N' : Rational-Neighborhood-Relation l2 A) →
    (N ＝ N') ≃ (Eq-Rational-Neighborhood-Relation N N')
  equiv-Eq-eq-Rational-Neighborhood-Relation N' =
    Eq-eq-Rational-Neighborhood-Relation N' ,
    is-fiberwise-equiv-Eq-eq-Rational-Neighborhood-Relation N'
```

### Characterization of the transport of rational neighborhood relations along equality of types

```agda
module _
  {l1 l2 : Level} (A : UU l1)
  where

  Eq-map-eq-tr-Rational-Neighborhood-Relation :
    (B : UU l1) (e : A ＝ B) (S : Rational-Neighborhood-Relation l2 A) →
    Eq-Rational-Neighborhood-Relation
      ( S)
      ( λ d x y →
        tr (Rational-Neighborhood-Relation l2) e S d (map-eq e x) (map-eq e y))
  Eq-map-eq-tr-Rational-Neighborhood-Relation .A refl S =
    refl-Eq-Rational-Neighborhood-Relation S

  eq-map-eq-tr-Rational-Neighborhood-Relation :
    (B : UU l1) (e : A ＝ B) (S : Rational-Neighborhood-Relation l2 A) →
    Id
      ( S)
      ( λ d x y →
        tr (Rational-Neighborhood-Relation l2) e S d (map-eq e x) (map-eq e y))
  eq-map-eq-tr-Rational-Neighborhood-Relation B e S =
    eq-Eq-Rational-Neighborhood-Relation
      ( S)
      ( λ d x y →
        tr (Rational-Neighborhood-Relation l2) e S d (map-eq e x) (map-eq e y))
      ( Eq-map-eq-tr-Rational-Neighborhood-Relation B e S)

  Eq-map-inv-eq-tr-Rational-Neighborhood-Relation :
    (B : UU l1) (e : A ＝ B) (S : Rational-Neighborhood-Relation l2 A) →
    Eq-Rational-Neighborhood-Relation
      ( tr (Rational-Neighborhood-Relation l2) e S)
      ( λ d x y → S d (map-inv-eq e x) (map-inv-eq e y))
  Eq-map-inv-eq-tr-Rational-Neighborhood-Relation .A refl S =
    refl-Eq-Rational-Neighborhood-Relation S

  eq-map-inv-eq-tr-Rational-Neighborhood-Relation :
    (B : UU l1) (e : A ＝ B) (S : Rational-Neighborhood-Relation l2 A) →
    Id
      ( tr (Rational-Neighborhood-Relation l2) e S)
      ( λ d x y → S d (map-inv-eq e x) (map-inv-eq e y))
  eq-map-inv-eq-tr-Rational-Neighborhood-Relation B e S =
    eq-Eq-Rational-Neighborhood-Relation
      ( tr (Rational-Neighborhood-Relation l2) e S)
      ( λ d x y → S d (map-inv-eq e x) (map-inv-eq e y))
      ( Eq-map-inv-eq-tr-Rational-Neighborhood-Relation B e S)
```

### The similarity relation induced by a rational neighborhood relation

```agda
module _ {l1 l2 : Level} {A : UU l1} (N : Rational-Neighborhood-Relation l2 A)
  where

  sim-prop-Rational-Neighborhood-Relation : Relation-Prop (l1 ⊔ l2) A
  sim-prop-Rational-Neighborhood-Relation x y =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( A)
          ( λ z →
            product-Prop
              ( N d x z ⇔ N d y z)
              ( N d z x ⇔ N d z y)))

  sim-Rational-Neighborhood-Relation : Relation (l1 ⊔ l2) A
  sim-Rational-Neighborhood-Relation x y =
    type-Prop (sim-prop-Rational-Neighborhood-Relation x y)

  is-prop-sim-Rational-Neighborhood-Relatiion :
    (x y : A) → is-prop (sim-Rational-Neighborhood-Relation x y)
  is-prop-sim-Rational-Neighborhood-Relatiion x y =
    is-prop-type-Prop (sim-prop-Rational-Neighborhood-Relation x y)

  iff-left-neighbor-sim-Rational-Neighborhood-Relation :
    {x y : A} →
    sim-Rational-Neighborhood-Relation x y →
    (d : ℚ⁺) (z : A) →
    neighborhood-Rational-Neighborhood-Relation N d x z ↔
    neighborhood-Rational-Neighborhood-Relation N d y z
  iff-left-neighbor-sim-Rational-Neighborhood-Relation x≍y d z =
    pr1 (x≍y d z)

  iff-right-neighbor-sim-Rational-Neighborhood-Relation :
    {x y : A} →
    sim-Rational-Neighborhood-Relation x y →
    (d : ℚ⁺) (z : A) →
    neighborhood-Rational-Neighborhood-Relation N d z x ↔
    neighborhood-Rational-Neighborhood-Relation N d z y
  iff-right-neighbor-sim-Rational-Neighborhood-Relation x≍y d z =
    pr2 (x≍y d z)

  refl-sim-Rational-Neighborhood-Relation :
    (x : A) → sim-Rational-Neighborhood-Relation x x
  refl-sim-Rational-Neighborhood-Relation x d z = id-iff , id-iff

  sim-eq-Rational-Neighborhood-Relation :
    (x y : A) → x ＝ y → sim-Rational-Neighborhood-Relation x y
  sim-eq-Rational-Neighborhood-Relation x .x refl =
    refl-sim-Rational-Neighborhood-Relation x

  symmetric-sim-Rational-Neighborhood-Relation :
    (x y : A) →
    sim-Rational-Neighborhood-Relation x y →
    sim-Rational-Neighborhood-Relation y x
  symmetric-sim-Rational-Neighborhood-Relation x y x≍y d z =
    ( inv-iff (iff-left-neighbor-sim-Rational-Neighborhood-Relation x≍y d z)) ,
    ( inv-iff (iff-right-neighbor-sim-Rational-Neighborhood-Relation x≍y d z))

  inv-sim-Rational-Neighborhood-Relation :
    {x y : A} →
    sim-Rational-Neighborhood-Relation x y →
    sim-Rational-Neighborhood-Relation y x
  inv-sim-Rational-Neighborhood-Relation {x} {y} =
    symmetric-sim-Rational-Neighborhood-Relation x y

  transitive-sim-Rational-Neighborhood-Relation :
    (x y z : A) →
    sim-Rational-Neighborhood-Relation y z →
    sim-Rational-Neighborhood-Relation x y →
    sim-Rational-Neighborhood-Relation x z
  transitive-sim-Rational-Neighborhood-Relation x y z y≍z x≍y d w =
    ( ( iff-left-neighbor-sim-Rational-Neighborhood-Relation y≍z d w) ∘iff
      ( iff-left-neighbor-sim-Rational-Neighborhood-Relation x≍y d w)) ,
    ( ( iff-right-neighbor-sim-Rational-Neighborhood-Relation y≍z d w) ∘iff
      ( iff-right-neighbor-sim-Rational-Neighborhood-Relation x≍y d w))

  is-equivalence-relation-sim-Rational-Neighborhood-Relation :
    is-equivalence-relation (sim-prop-Rational-Neighborhood-Relation)
  is-equivalence-relation-sim-Rational-Neighborhood-Relation =
    refl-sim-Rational-Neighborhood-Relation ,
    symmetric-sim-Rational-Neighborhood-Relation ,
    transitive-sim-Rational-Neighborhood-Relation

  equivalence-sim-Rational-Neighborhood-Relation :
    equivalence-relation (l1 ⊔ l2) A
  equivalence-sim-Rational-Neighborhood-Relation =
    sim-prop-Rational-Neighborhood-Relation ,
    is-equivalence-relation-sim-Rational-Neighborhood-Relation
```

### Similar elements have equivalent self-neighborhoods

```agda
module _
  {l1 l2 : Level} {A : UU l1} (N : Rational-Neighborhood-Relation l2 A)
  where

  iff-self-neighborhood-sim-Rational-Neighborhood-Relation :
    (d : ℚ⁺) (x y : A) →
    sim-Rational-Neighborhood-Relation N x y →
    neighborhood-Rational-Neighborhood-Relation N d x x ↔
    neighborhood-Rational-Neighborhood-Relation N d y y
  iff-self-neighborhood-sim-Rational-Neighborhood-Relation d x y x≍y =
    ( iff-right-neighbor-sim-Rational-Neighborhood-Relation N x≍y d y) ∘iff
    ( iff-left-neighbor-sim-Rational-Neighborhood-Relation N x≍y d x)
```
