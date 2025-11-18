# Heyting fields

```agda
module commutative-algebra.heyting-fields where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.invertible-elements-commutative-rings
open import commutative-algebra.local-commutative-rings
open import commutative-algebra.trivial-commutative-rings

open import foundation.apartness-relations
open import foundation.binary-relations
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.tight-apartness-relations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups

open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "Heyting field" WDID=Q5749811 WD="Heyting field" Agda=Heyting-Field}}
is a [local commutative ring](commutative-algebra.local-commutative-rings.md)
with the properties:

- it is [nontrivial](commutative-algebra.trivial-commutative-rings.md): 0 ≠ 1
- any
  [non](foundation.negation.md)-[invertible](commutative-algebra.invertible-elements-commutative-rings.md)
  element is [equal](foundation.identity-types.md) to zero

Note that this is distinct from the classical notion of a field, called
[discrete field](commutative-algebra.discrete-fields.md) in constructive
contexts, which asserts that every element is
[either](foundation.exclusive-disjunction.md) invertible or equal to zero. A
Heyting field is a discrete field if and only if its equality relation is
[decidable](foundation.decidable-equality.md), which would not include e.g. the
[real numbers](real-numbers.dedekind-real-numbers.md).

## Definition

```agda
is-heyting-field-prop-Local-Commutative-Ring :
  {l : Level} → Local-Commutative-Ring l → Prop l
is-heyting-field-prop-Local-Commutative-Ring R =
  ( is-nontrivial-commutative-ring-Prop
    ( commutative-ring-Local-Commutative-Ring R)) ∧
  ( Π-Prop
    ( type-Local-Commutative-Ring R)
    ( λ x →
      hom-Prop
        ( ¬'
          ( is-invertible-element-prop-Commutative-Ring
            ( commutative-ring-Local-Commutative-Ring R)
            ( x)))
        ( is-zero-prop-Local-Commutative-Ring R x)))

is-heyting-field-Local-Commutative-Ring :
  {l : Level} → Local-Commutative-Ring l → UU l
is-heyting-field-Local-Commutative-Ring R =
  type-Prop (is-heyting-field-prop-Local-Commutative-Ring R)

Heyting-Field : (l : Level) → UU (lsuc l)
Heyting-Field l =
  type-subtype (is-heyting-field-prop-Local-Commutative-Ring {l})
```

## Properties

```agda
module _
  {l : Level}
  (F : Heyting-Field l)
  where

  local-commutative-ring-Heyting-Field : Local-Commutative-Ring l
  local-commutative-ring-Heyting-Field = pr1 F

  commutative-ring-Heyting-Field : Commutative-Ring l
  commutative-ring-Heyting-Field =
    commutative-ring-Local-Commutative-Ring local-commutative-ring-Heyting-Field

  is-local-commutative-ring-Heyting-Field :
    is-local-Commutative-Ring commutative-ring-Heyting-Field
  is-local-commutative-ring-Heyting-Field =
    is-local-commutative-ring-Local-Commutative-Ring
      ( local-commutative-ring-Heyting-Field)

  ring-Heyting-Field : Ring l
  ring-Heyting-Field = ring-Commutative-Ring commutative-ring-Heyting-Field

  ab-Heyting-Field : Ab l
  ab-Heyting-Field = ab-Ring ring-Heyting-Field

  type-Heyting-Field : UU l
  type-Heyting-Field = type-Ring ring-Heyting-Field

  set-Heyting-Field : Set l
  set-Heyting-Field = set-Ring ring-Heyting-Field

  zero-Heyting-Field : type-Heyting-Field
  zero-Heyting-Field = zero-Ring ring-Heyting-Field

  is-zero-Heyting-Field : type-Heyting-Field → UU l
  is-zero-Heyting-Field = is-zero-Ring ring-Heyting-Field

  one-Heyting-Field : type-Heyting-Field
  one-Heyting-Field = one-Ring ring-Heyting-Field

  add-Heyting-Field :
    type-Heyting-Field → type-Heyting-Field → type-Heyting-Field
  add-Heyting-Field = add-Ring ring-Heyting-Field

  mul-Heyting-Field :
    type-Heyting-Field → type-Heyting-Field → type-Heyting-Field
  mul-Heyting-Field = mul-Ring ring-Heyting-Field

  neg-Heyting-Field : type-Heyting-Field → type-Heyting-Field
  neg-Heyting-Field = neg-Ring ring-Heyting-Field

  diff-Heyting-Field :
    type-Heyting-Field → type-Heyting-Field → type-Heyting-Field
  diff-Heyting-Field x y =
    add-Heyting-Field x (neg-Heyting-Field y)

  is-invertible-element-prop-Heyting-Field : type-Heyting-Field → Prop l
  is-invertible-element-prop-Heyting-Field =
    is-invertible-element-prop-Commutative-Ring commutative-ring-Heyting-Field

  is-invertible-element-Heyting-Field : type-Heyting-Field → UU l
  is-invertible-element-Heyting-Field x =
    type-Prop (is-invertible-element-prop-Heyting-Field x)

  is-zero-is-not-invertible-element-Heyting-Field :
    (x : type-Heyting-Field) → ¬ (is-invertible-element-Heyting-Field x) →
    is-zero-Heyting-Field x
  is-zero-is-not-invertible-element-Heyting-Field = pr2 (pr2 F)

  is-nontrivial-commutative-ring-Heyting-Field :
    is-nontrivial-Commutative-Ring commutative-ring-Heyting-Field
  is-nontrivial-commutative-ring-Heyting-Field = pr1 (pr2 F)

  right-inverse-law-add-Heyting-Field :
    (x : type-Heyting-Field) → diff-Heyting-Field x x ＝ zero-Heyting-Field
  right-inverse-law-add-Heyting-Field =
    right-inverse-law-add-Ring ring-Heyting-Field

  left-zero-law-mul-Heyting-Field :
    (x : type-Heyting-Field) →
    mul-Heyting-Field zero-Heyting-Field x ＝ zero-Heyting-Field
  left-zero-law-mul-Heyting-Field = left-zero-law-mul-Ring ring-Heyting-Field

  ap-mul-Heyting-Field :
    {x x' y y' : type-Heyting-Field} → x ＝ x' → y ＝ y' →
    mul-Heyting-Field x y ＝ mul-Heyting-Field x' y'
  ap-mul-Heyting-Field = ap-mul-Ring ring-Heyting-Field

  mul-neg-Heyting-Field :
    (x y : type-Heyting-Field) →
    mul-Heyting-Field (neg-Heyting-Field x) (neg-Heyting-Field y) ＝
    mul-Heyting-Field x y
  mul-neg-Heyting-Field = mul-neg-Ring ring-Heyting-Field

  distributive-neg-diff-Heyting-Field :
    (x y : type-Heyting-Field) →
    neg-Heyting-Field (diff-Heyting-Field x y) ＝ diff-Heyting-Field y x
  distributive-neg-diff-Heyting-Field =
    neg-right-subtraction-Ab ab-Heyting-Field

  commutative-mul-Heyting-Field :
    (x y : type-Heyting-Field) → mul-Heyting-Field x y ＝ mul-Heyting-Field y x
  commutative-mul-Heyting-Field =
    commutative-mul-Commutative-Ring commutative-ring-Heyting-Field

  add-diff-Heyting-Field :
    (x y z : type-Heyting-Field) →
    add-Heyting-Field (diff-Heyting-Field x y) (diff-Heyting-Field y z) ＝
    diff-Heyting-Field x z
  add-diff-Heyting-Field =
    add-right-subtraction-Ab ab-Heyting-Field

  eq-is-zero-diff-Heyting-Field :
    (x y : type-Heyting-Field) →
    is-zero-Heyting-Field (diff-Heyting-Field x y) →
    x ＝ y
  eq-is-zero-diff-Heyting-Field x y =
    eq-is-zero-right-subtraction-Ab ab-Heyting-Field
```

## Properties

### Invertibility of `x - y` is a tight apartness relation

```agda
module _
  {l : Level}
  (F : Heyting-Field l)
  where

  apart-prop-Heyting-Field : Relation-Prop l (type-Heyting-Field F)
  apart-prop-Heyting-Field x y =
    is-invertible-element-prop-Heyting-Field F (diff-Heyting-Field F x y)

  apart-Heyting-Field : Relation l (type-Heyting-Field F)
  apart-Heyting-Field = type-Relation-Prop apart-prop-Heyting-Field

  abstract
    antirefl-apart-Heyting-Field : is-antireflexive apart-prop-Heyting-Field
    antirefl-apart-Heyting-Field x (y , ⟨x-x⟩y=1 , _) =
      is-nontrivial-commutative-ring-Heyting-Field
        ( F)
        ( equational-reasoning
          zero-Heyting-Field F
          ＝ mul-Heyting-Field F (zero-Heyting-Field F) y
            by inv (left-zero-law-mul-Heyting-Field F y)
          ＝ mul-Heyting-Field F (diff-Heyting-Field F x x) y
            by
              ap-mul-Heyting-Field F
                ( inv (right-inverse-law-add-Heyting-Field F x))
                ( refl)
          ＝ one-Heyting-Field F
            by ⟨x-x⟩y=1)

    symmetric-apart-Heyting-Field : is-symmetric apart-Heyting-Field
    symmetric-apart-Heyting-Field x y (z , ⟨x-y⟩z=1 , z⟨x-y⟩=1) =
      let
        ⟨y-x⟩⟨-z⟩=1 =
          equational-reasoning
            mul-Heyting-Field F
              ( diff-Heyting-Field F y x)
              ( neg-Heyting-Field F z)
            ＝
              mul-Heyting-Field F
                ( neg-Heyting-Field F (diff-Heyting-Field F x y))
                ( neg-Heyting-Field F z)
              by
                ap-mul-Heyting-Field F
                  ( inv (distributive-neg-diff-Heyting-Field F x y))
                  ( refl)
            ＝ mul-Heyting-Field F (diff-Heyting-Field F x y) z
              by mul-neg-Heyting-Field F _ _
            ＝ one-Heyting-Field F
              by ⟨x-y⟩z=1
      in
        ( neg-Heyting-Field F z ,
          ⟨y-x⟩⟨-z⟩=1 ,
          commutative-mul-Heyting-Field F _ _ ∙ ⟨y-x⟩⟨-z⟩=1)

    cotransitive-apart-Heyting-Field :
      is-cotransitive apart-prop-Heyting-Field
    cotransitive-apart-Heyting-Field x y z is-invertible-⟨x-y⟩ =
      map-disjunction
        ( id)
        ( symmetric-apart-Heyting-Field z y)
        ( is-local-commutative-ring-Heyting-Field F
          ( diff-Heyting-Field F x z)
          ( diff-Heyting-Field F z y)
          ( inv-tr
            ( is-invertible-element-Heyting-Field F)
            ( add-diff-Heyting-Field F x z y)
            ( is-invertible-⟨x-y⟩)))

  apartness-relation-Heyting-Field : Apartness-Relation l (type-Heyting-Field F)
  apartness-relation-Heyting-Field =
    ( apart-prop-Heyting-Field ,
      antirefl-apart-Heyting-Field ,
      symmetric-apart-Heyting-Field ,
      cotransitive-apart-Heyting-Field)

  abstract
    is-tight-apartness-relation-Heyting-Field :
      is-tight-Apartness-Relation apartness-relation-Heyting-Field
    is-tight-apartness-relation-Heyting-Field x y ¬apart-x-y =
      eq-is-zero-diff-Heyting-Field F
        ( x)
        ( y)
        ( is-zero-is-not-invertible-element-Heyting-Field F
          ( diff-Heyting-Field F x y)
          ( ¬apart-x-y))

  tight-apartness-relation-Heyting-Field :
    Tight-Apartness-Relation l (type-Heyting-Field F)
  tight-apartness-relation-Heyting-Field =
    ( apartness-relation-Heyting-Field ,
      is-tight-apartness-relation-Heyting-Field)
```

## External links

- [Heyting field](https://ncatlab.org/nlab/show/Heyting+field) at $n$Lab
