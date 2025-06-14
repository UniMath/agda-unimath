# Rational neighborhood relations on types

```agda
module metric-spaces.rational-neighborhoods where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.empty-types
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
{{#concept "upper bound" Disambiguation="on the distance with respect to a rational neighborhood relation"}}
on the distance between `x` and `y` with respect to the rational neighborhood
relation.

## Definitions

### Rational neighborhood relation on a type

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

  is-torsorial-Eq-Rational-Neighborhood-Relation :
    is-torsorial (Eq-Rational-Neighborhood-Relation N)
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
