# Conjugation by invertible elements in monoids

```agda
module group-theory.conjugation-invertible-elements-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.invertible-elements-monoids
open import group-theory.monoids

open import logic.functoriality-existential-quantification
```

</details>

## Idea

If `x` is an [invertible element](group-theory.invertible-elements-monoids.md)
of a [monoid](group-theory.monoids.md) `M`, then the
{{#concept "conjugation" Disambiguation="by an invertible element of a monoid"}}
of `y` by `x` is `x⁻¹yx`. If there
[exists](foundation.existential-quantification.md) an `x` such that `x⁻¹yx = z`,
then `y` and `z` are said to be conjugate, which forms an
[equivalence relation](foundation.equivalence-relations.md) on the elements of
`M`.

## Definition

### Conjugation by an invertible element

```agda
module _
  {l : Level}
  (M : Monoid l)
  where

  left-conjugation-invertible-element-Monoid :
    invertible-element-Monoid M → type-Monoid M → type-Monoid M
  left-conjugation-invertible-element-Monoid (x , x⁻¹ , _) y =
    mul-Monoid M x⁻¹ (mul-Monoid M y x)

  right-conjugation-invertible-element-Monoid :
    invertible-element-Monoid M → type-Monoid M → type-Monoid M
  right-conjugation-invertible-element-Monoid (x , x⁻¹ , _) y =
    mul-Monoid M (mul-Monoid M x⁻¹ y) x
```

### Conjugacy by an invertible element

```agda
module _
  {l : Level}
  (M : Monoid l)
  where

  is-conjugate-prop-invertible-element-Monoid :
    Relation-Prop l (type-Monoid M)
  is-conjugate-prop-invertible-element-Monoid x y =
    ∃ ( invertible-element-Monoid M)
      ( λ z →
        Id-Prop
          ( set-Monoid M)
          ( left-conjugation-invertible-element-Monoid M z x)
          ( y))

  is-conjugate-invertible-element-Monoid :
    Relation l (type-Monoid M)
  is-conjugate-invertible-element-Monoid =
    type-Relation-Prop is-conjugate-prop-invertible-element-Monoid
```

## Properties

### Left and right conjugation are equivalent

```agda
module _
  {l : Level}
  (M : Monoid l)
  (xi@(x , x⁻¹ , _) : invertible-element-Monoid M)
  where

  abstract
    htpy-left-right-conjugation-invertible-element-Monoid :
      left-conjugation-invertible-element-Monoid M xi ~
      right-conjugation-invertible-element-Monoid M xi
    htpy-left-right-conjugation-invertible-element-Monoid y =
      inv (associative-mul-Monoid M x⁻¹ y x)

    eq-left-right-conjugation-invertible-element-Monoid :
      left-conjugation-invertible-element-Monoid M xi ＝
      right-conjugation-invertible-element-Monoid M xi
    eq-left-right-conjugation-invertible-element-Monoid =
      eq-htpy htpy-left-right-conjugation-invertible-element-Monoid
```

### Conjugation by an invertible element is an equivalence

```agda
module _
  {l : Level}
  (M : Monoid l)
  (xi@(x , x⁻¹ , is-inv-x⁻¹) : invertible-element-Monoid M)
  where

  is-equiv-left-conjugation-invertible-element-Monoid :
    is-equiv (left-conjugation-invertible-element-Monoid M xi)
  is-equiv-left-conjugation-invertible-element-Monoid =
    is-equiv-comp
      ( mul-Monoid M x⁻¹)
      ( mul-Monoid' M x)
      ( is-equiv-mul-is-invertible-element-Monoid' M (x⁻¹ , is-inv-x⁻¹))
      ( is-equiv-mul-is-invertible-element-Monoid
        ( M)
        ( is-invertible-element-inv-is-invertible-element-Monoid
          ( M)
          ( x⁻¹ , is-inv-x⁻¹)))

  is-equiv-right-conjugation-invertible-element-Monoid :
    is-equiv (right-conjugation-invertible-element-Monoid M xi)
  is-equiv-right-conjugation-invertible-element-Monoid =
    is-equiv-comp
      ( mul-Monoid' M x)
      ( mul-Monoid M x⁻¹)
      ( is-equiv-mul-is-invertible-element-Monoid
        ( M)
        ( is-invertible-element-inv-is-invertible-element-Monoid
          ( M)
          ( x⁻¹ , is-inv-x⁻¹)))
      ( is-equiv-mul-is-invertible-element-Monoid' M (x⁻¹ , is-inv-x⁻¹))

  equiv-left-conjugation-invertible-element-Monoid :
    type-Monoid M ≃ type-Monoid M
  equiv-left-conjugation-invertible-element-Monoid =
    ( left-conjugation-invertible-element-Monoid M xi ,
      is-equiv-left-conjugation-invertible-element-Monoid)

  equiv-right-conjugation-invertible-element-Monoid :
    type-Monoid M ≃ type-Monoid M
  equiv-right-conjugation-invertible-element-Monoid =
    ( right-conjugation-invertible-element-Monoid M xi ,
      is-equiv-right-conjugation-invertible-element-Monoid)
```

### Conjugation by the identity is the identity

```agda
module _
  {l : Level}
  (M : Monoid l)
  where

  abstract
    left-conjugation-unit-Monoid :
      (x : type-Monoid M) →
      left-conjugation-invertible-element-Monoid
        ( M)
        ( invertible-element-unit-Monoid M)
        ( x) ＝
      x
    left-conjugation-unit-Monoid x =
      left-unit-law-mul-Monoid M _ ∙ right-unit-law-mul-Monoid M _

    right-conjugation-unit-Monoid :
      (x : type-Monoid M) →
      right-conjugation-invertible-element-Monoid
        ( M)
        ( invertible-element-unit-Monoid M)
        ( x) ＝
      x
    right-conjugation-unit-Monoid x =
      right-unit-law-mul-Monoid M _ ∙ left-unit-law-mul-Monoid M _
```

### Conjugation by `p` followed by conjugation by `q` is conjugation by `pq`

```agda
module _
  {l : Level}
  (M : Monoid l)
  where

  abstract
    double-left-conjugation-invertible-element-Monoid :
      (p q : invertible-element-Monoid M)
      (x : type-Monoid M) →
      left-conjugation-invertible-element-Monoid M
        ( q)
        ( left-conjugation-invertible-element-Monoid M p x) ＝
      left-conjugation-invertible-element-Monoid M
        ( mul-invertible-element-Monoid M p q)
        ( x)
    double-left-conjugation-invertible-element-Monoid
      (p , p⁻¹ , _) (q , q⁻¹ , _) x =
      let
        _*M_ = mul-Monoid M
      in
        equational-reasoning
          q⁻¹ *M ((p⁻¹ *M (x *M p)) *M q)
          ＝ q⁻¹ *M (p⁻¹ *M ((x *M p) *M q))
            by ap-mul-Monoid M refl (associative-mul-Monoid M _ _ _)
          ＝ (q⁻¹ *M p⁻¹) *M ((x *M p) *M q)
            by inv (associative-mul-Monoid M _ _ _)
          ＝ (q⁻¹ *M p⁻¹) *M (x *M (p *M q))
            by ap-mul-Monoid M refl (associative-mul-Monoid M x p q)
```

### Conjugation by an element and its inverse is the identity

```agda
module _
  {l : Level}
  (M : Monoid l)
  (xi@(x , is-invertible-x@(x⁻¹ , _ , _)) : invertible-element-Monoid M)
  where

  abstract
    left-conjugation-inv-left-conjugation-invertible-element-Monoid :
      (y : type-Monoid M) →
      left-conjugation-invertible-element-Monoid
        ( M)
        ( invertible-element-inv-invertible-element-Monoid M xi)
        ( left-conjugation-invertible-element-Monoid M xi y) ＝
      y
    left-conjugation-inv-left-conjugation-invertible-element-Monoid y =
      let
        xi⁻¹ = invertible-element-inv-invertible-element-Monoid M xi
      in
        ( double-left-conjugation-invertible-element-Monoid M xi xi⁻¹ y) ∙
        ( ap-binary
          ( left-conjugation-invertible-element-Monoid M)
          ( eq-type-subtype
            ( is-invertible-element-prop-Monoid M)
            { a = mul-invertible-element-Monoid M xi xi⁻¹}
            { b = invertible-element-unit-Monoid M}
            ( is-right-inverse-inv-is-invertible-element-Monoid
              ( M)
              ( is-invertible-x)))
          ( refl)) ∙
        ( left-conjugation-unit-Monoid M y)
```

### Conjugacy by an invertible element is reflexive

```agda
module _
  {l : Level}
  (M : Monoid l)
  where

  abstract
    refl-is-conjugate-invertible-element-Monoid :
      is-reflexive (is-conjugate-invertible-element-Monoid M)
    refl-is-conjugate-invertible-element-Monoid x =
      intro-exists
        ( invertible-element-unit-Monoid M)
        ( left-conjugation-unit-Monoid M x)
```

### Conjugacy by an invertible element is symmetric

```agda
module _
  {l : Level}
  (M : Monoid l)
  where

  abstract
    symmetric-is-conjugate-invertible-element-Monoid :
      is-symmetric (is-conjugate-invertible-element-Monoid M)
    symmetric-is-conjugate-invertible-element-Monoid x y =
      map-exists
        ( λ z' → left-conjugation-invertible-element-Monoid M z' y ＝ x)
        ( invertible-element-inv-invertible-element-Monoid M)
        ( λ zi z⁻¹⟨xz⟩=y →
          ( ap
            ( left-conjugation-invertible-element-Monoid
              ( M)
              ( invertible-element-inv-invertible-element-Monoid M zi))
            ( inv z⁻¹⟨xz⟩=y)) ∙
          ( left-conjugation-inv-left-conjugation-invertible-element-Monoid
            ( M)
            ( zi)
            ( x)))
```

### Conjugacy by an invertible element is transitive

```agda
module _
  {l : Level}
  (M : Monoid l)
  where

  abstract
    transitive-is-conjugate-invertible-element-Monoid :
      is-transitive (is-conjugate-invertible-element-Monoid M)
    transitive-is-conjugate-invertible-element-Monoid x y z y~z x~y =
      let
        open
          do-syntax-trunc-Prop
            ( is-conjugate-prop-invertible-element-Monoid M x z)
        _*M_ = mul-Monoid M
      in do
        (p , p⁻¹⟨xp⟩=y) ← x~y
        (q , q⁻¹⟨yq⟩=z) ← y~z
        intro-exists
          ( mul-invertible-element-Monoid M p q)
          ( ( inv
              ( double-left-conjugation-invertible-element-Monoid
                ( M)
                ( p)
                ( q)
                ( x))) ∙
            ( ap (left-conjugation-invertible-element-Monoid M q) p⁻¹⟨xp⟩=y) ∙
            ( q⁻¹⟨yq⟩=z))
```

### Conjugacy by an invertible element is an equivalence relation

```agda
module _
  {l : Level}
  (M : Monoid l)
  where

  equivalence-relation-is-conjugate-invertible-element-Monoid :
    equivalence-relation l (type-Monoid M)
  equivalence-relation-is-conjugate-invertible-element-Monoid =
    ( is-conjugate-prop-invertible-element-Monoid M ,
      refl-is-conjugate-invertible-element-Monoid M ,
      symmetric-is-conjugate-invertible-element-Monoid M ,
      transitive-is-conjugate-invertible-element-Monoid M)
```
