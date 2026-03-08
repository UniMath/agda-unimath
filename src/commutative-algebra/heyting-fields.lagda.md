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

open import foundation.action-on-identifications-binary-functions
open import foundation.apartness-relations
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.logical-equivalences
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

  ap-add-Heyting-Field :
    {x x' : type-Heyting-Field} →
    x ＝ x' →
    {y y' : type-Heyting-Field} →
    y ＝ y' →
    add-Heyting-Field x y ＝
    add-Heyting-Field x' y'
  ap-add-Heyting-Field = ap-binary add-Heyting-Field

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

  is-invertible-is-right-invertible-element-Heyting-Field :
    {x : type-Heyting-Field} →
    is-right-invertible-element-Commutative-Ring
      ( commutative-ring-Heyting-Field)
      ( x) →
    is-invertible-element-Heyting-Field x
  is-invertible-is-right-invertible-element-Heyting-Field =
    is-invertible-is-right-invertible-element-Commutative-Ring
      ( commutative-ring-Heyting-Field)

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

  associative-mul-Heyting-Field :
    (x y z : type-Heyting-Field) →
    mul-Heyting-Field (mul-Heyting-Field x y) z ＝
    mul-Heyting-Field x (mul-Heyting-Field y z)
  associative-mul-Heyting-Field =
    associative-mul-Commutative-Ring commutative-ring-Heyting-Field

  commutative-mul-Heyting-Field :
    (x y : type-Heyting-Field) → mul-Heyting-Field x y ＝ mul-Heyting-Field y x
  commutative-mul-Heyting-Field =
    commutative-mul-Commutative-Ring commutative-ring-Heyting-Field

  left-distributive-mul-diff-Heyting-Field :
    (x y z : type-Heyting-Field) →
    mul-Heyting-Field x (diff-Heyting-Field y z) ＝
    diff-Heyting-Field (mul-Heyting-Field x y) (mul-Heyting-Field x z)
  left-distributive-mul-diff-Heyting-Field =
    left-distributive-mul-right-subtraction-Commutative-Ring
      ( commutative-ring-Heyting-Field)

  right-distributive-mul-diff-Heyting-Field :
    (x y z : type-Heyting-Field) →
    mul-Heyting-Field (diff-Heyting-Field x y) z ＝
    diff-Heyting-Field (mul-Heyting-Field x z) (mul-Heyting-Field y z)
  right-distributive-mul-diff-Heyting-Field =
    right-distributive-mul-right-subtraction-Commutative-Ring
      ( commutative-ring-Heyting-Field)

  add-diff-Heyting-Field :
    (x y z : type-Heyting-Field) →
    add-Heyting-Field (diff-Heyting-Field x y) (diff-Heyting-Field y z) ＝
    diff-Heyting-Field x z
  add-diff-Heyting-Field =
    add-right-subtraction-Ab ab-Heyting-Field

  diff-add-Heyting-Field :
    (z x y : type-Heyting-Field) →
    diff-Heyting-Field (add-Heyting-Field x z) (add-Heyting-Field y z) ＝
    diff-Heyting-Field x y
  diff-add-Heyting-Field = right-subtraction-right-add-Ab ab-Heyting-Field

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
    antirefl-apart-Heyting-Field x is-invertible-x-x =
      is-nontrivial-commutative-ring-Heyting-Field
        ( F)
        ( is-trivial-is-invertible-zero-Commutative-Ring
          ( commutative-ring-Heyting-Field F)
          ( tr
            ( is-invertible-element-Heyting-Field F)
            ( right-inverse-law-add-Heyting-Field F x)
            ( is-invertible-x-x)))

    symmetric-apart-Heyting-Field : is-symmetric apart-Heyting-Field
    symmetric-apart-Heyting-Field x y is-invertible-⟨x-y⟩ =
      tr
        ( is-invertible-element-Heyting-Field F)
        ( distributive-neg-diff-Heyting-Field F x y)
        ( is-invertible-element-neg-is-invertible-element-Commutative-Ring
          ( commutative-ring-Heyting-Field F)
          ( _)
          ( is-invertible-⟨x-y⟩))

    cotransitive-apart-Heyting-Field :
      is-cotransitive apart-prop-Heyting-Field
    cotransitive-apart-Heyting-Field x y z is-invertible-⟨x-z⟩ =
      is-local-commutative-ring-Heyting-Field F
        ( diff-Heyting-Field F x y)
        ( diff-Heyting-Field F y z)
        ( inv-tr
          ( is-invertible-element-Heyting-Field F)
          ( add-diff-Heyting-Field F x y z)
          ( is-invertible-⟨x-z⟩))

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

### Extensionality of the apartness relation on addition

```agda
module _
  {l : Level}
  (F : Heyting-Field l)
  where

  abstract
    extensional-add-apart-Heyting-Field :
      is-extensional-binary-op-Apartness-Relation
        ( add-Heyting-Field F)
        ( apartness-relation-Heyting-Field F)
    extensional-add-apart-Heyting-Field w x y z w+x#y+z =
      is-local-commutative-ring-Heyting-Field F
        ( diff-Heyting-Field F w y)
        ( diff-Heyting-Field F x z)
        ( tr
          ( is-invertible-element-Heyting-Field F)
          ( interchange-add-right-subtraction-Commutative-Ring
            ( commutative-ring-Heyting-Field F)
            ( w)
            ( x)
            ( y)
            ( z))
          ( w+x#y+z))
```

### Addition preserves and reflects apartness

```agda
module _
  {l : Level}
  (F : Heyting-Field l)
  where

  abstract
    preserves-apart-right-add-Heyting-Field :
      (z x y : type-Heyting-Field F) →
      apart-Heyting-Field F x y →
      apart-Heyting-Field F (add-Heyting-Field F x z) (add-Heyting-Field F y z)
    preserves-apart-right-add-Heyting-Field z x y =
      inv-tr
        ( is-invertible-element-Heyting-Field F)
        ( diff-add-Heyting-Field F z x y)

    reflects-apart-right-add-Heyting-Field :
      (z x y : type-Heyting-Field F) →
      apart-Heyting-Field F
        ( add-Heyting-Field F x z)
        ( add-Heyting-Field F y z) →
      apart-Heyting-Field F x y
    reflects-apart-right-add-Heyting-Field z x y x+z#y+z =
      binary-tr
        ( apart-Heyting-Field F)
        ( is-retraction-right-subtraction-Ab (ab-Heyting-Field F) z x)
        ( is-retraction-right-subtraction-Ab (ab-Heyting-Field F) z y)
        ( preserves-apart-right-add-Heyting-Field
          ( neg-Heyting-Field F z)
          ( add-Heyting-Field F x z)
          ( add-Heyting-Field F y z)
          ( x+z#y+z))
```

### Extensionality of the apartness relation on multiplication

```agda
module _
  {l : Level}
  (F : Heyting-Field l)
  (let _*F_ = mul-Heyting-Field F)
  (let _-F_ = diff-Heyting-Field F)
  where

  abstract
    extensional-apart-mul-Heyting-Field :
      is-extensional-binary-op-Apartness-Relation
        ( mul-Heyting-Field F)
        ( apartness-relation-Heyting-Field F)
    extensional-apart-mul-Heyting-Field w x y z wx#yz =
      map-disjunction
        ( λ (⟨wx-yx⟩⁻¹ , ⟨wx-yx⟩⟨wx-yx⟩⁻¹=1 , _) →
          is-invertible-is-right-invertible-element-Heyting-Field F
            ( x *F ⟨wx-yx⟩⁻¹ ,
              ( equational-reasoning
                (w -F y) *F (x *F ⟨wx-yx⟩⁻¹)
                ＝ ((w -F y) *F x) *F ⟨wx-yx⟩⁻¹
                  by inv (associative-mul-Heyting-Field F _ _ _)
                ＝ ((w *F x) -F (y *F x)) *F ⟨wx-yx⟩⁻¹
                  by
                    ap-mul-Heyting-Field F
                      ( right-distributive-mul-diff-Heyting-Field F w y x)
                      ( refl)
                ＝ one-Heyting-Field F
                  by ⟨wx-yx⟩⟨wx-yx⟩⁻¹=1)))
        ( λ (⟨yx-yz⟩⁻¹ , ⟨yx-yz⟩⟨yx-yz⟩⁻¹=1 , _) →
          is-invertible-is-right-invertible-element-Heyting-Field F
            ( y *F ⟨yx-yz⟩⁻¹ ,
              ( equational-reasoning
                (x -F z) *F (y *F ⟨yx-yz⟩⁻¹)
                ＝ ((x -F z) *F y) *F ⟨yx-yz⟩⁻¹
                  by inv (associative-mul-Heyting-Field F _ _ _)
                ＝ (y *F (x -F z)) *F ⟨yx-yz⟩⁻¹
                  by
                    ap-mul-Heyting-Field F
                      ( commutative-mul-Heyting-Field F _ _)
                      ( refl)
                ＝ ((y *F x) -F (y *F z)) *F ⟨yx-yz⟩⁻¹
                  by
                    ap-mul-Heyting-Field F
                      ( left-distributive-mul-diff-Heyting-Field F y x z)
                      ( refl)
                ＝ one-Heyting-Field F
                  by ⟨yx-yz⟩⟨yx-yz⟩⁻¹=1)))
        ( cotransitive-apart-Heyting-Field F
          ( mul-Heyting-Field F w x)
          ( mul-Heyting-Field F y x)
          ( mul-Heyting-Field F y z)
          ( wx#yz))
```

### A Heyting field can be defined in terms of a commutative ring with a tight apartness relation, where addition is apartness-extensional and apartness characterizes invertibiltiy

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : Tight-Apartness-Relation l2 (type-Commutative-Ring R))
  (extensional-addition-apartness :
    is-extensional-binary-op-Apartness-Relation
      ( add-Commutative-Ring R)
      ( apartness-relation-Tight-Apartness-Relation A))
  (inv-iff-apart-zero :
    (x : type-Commutative-Ring R) →
    ( is-invertible-element-Commutative-Ring R x ↔
      apart-Tight-Apartness-Relation A x (zero-Commutative-Ring R)))
  (let _+R_ = add-Commutative-Ring R)
  (let neg-R = neg-Commutative-Ring R)
  (let _-R_ = right-subtraction-Commutative-Ring R)
  (let zero-R = zero-Commutative-Ring R)
  where

  abstract
    preserves-apart-right-add-tight-apartness-relation-Commutative-Ring :
      (z x y : type-Commutative-Ring R) →
      apart-Tight-Apartness-Relation A x y →
      apart-Tight-Apartness-Relation A
        ( add-Commutative-Ring R x z)
        ( add-Commutative-Ring R y z)
    preserves-apart-right-add-tight-apartness-relation-Commutative-Ring
      z x y x#y =
      elim-disjunction
        ( rel-Tight-Apartness-Relation A _ _)
        ( id)
        ( λ -z#-z → ex-falso (antirefl-Tight-Apartness-Relation A _ -z#-z))
        ( extensional-addition-apartness
          ( x +R z)
          ( neg-R z)
          ( y +R z)
          ( neg-R z)
          ( binary-tr
            ( apart-Tight-Apartness-Relation A)
            ( inv
              ( is-retraction-right-subtraction-Ab (ab-Commutative-Ring R) z x))
            ( inv
              ( is-retraction-right-subtraction-Ab (ab-Commutative-Ring R) z y))
            ( x#y)))

    apart-is-invertible-diff-tight-apartness-relation-Commutative-Ring :
      (x y : type-Commutative-Ring R) →
      is-invertible-element-Commutative-Ring R
        ( right-subtraction-Commutative-Ring R x y) →
      apart-Tight-Apartness-Relation A x y
    apart-is-invertible-diff-tight-apartness-relation-Commutative-Ring
      x y is-invertible-⟨x-y⟩ =
      binary-tr
        ( apart-Tight-Apartness-Relation A)
        ( is-section-right-subtraction-Commutative-Ring R y x)
        ( left-unit-law-add-Commutative-Ring R y)
        ( preserves-apart-right-add-tight-apartness-relation-Commutative-Ring
          ( y)
          ( x -R y)
          ( zero-Commutative-Ring R)
          ( forward-implication
            ( inv-iff-apart-zero (right-subtraction-Commutative-Ring R x y))
            ( is-invertible-⟨x-y⟩)))

    is-invertible-diff-apart-tight-apartness-relation-Commutative-Ring :
      (x y : type-Commutative-Ring R) →
      apart-Tight-Apartness-Relation A x y →
      is-invertible-element-Commutative-Ring R
        ( right-subtraction-Commutative-Ring R x y)
    is-invertible-diff-apart-tight-apartness-relation-Commutative-Ring x y x#y =
      backward-implication
        ( inv-iff-apart-zero _)
        ( binary-tr
          ( apart-Tight-Apartness-Relation A)
          ( refl)
          ( right-inverse-law-add-Commutative-Ring R y)
          ( preserves-apart-right-add-tight-apartness-relation-Commutative-Ring
            ( neg-Commutative-Ring R y)
            ( x)
            ( y)
            ( x#y)))

    is-local-commutative-ring-tight-apartness-relation-Commutative-Ring :
      is-local-Commutative-Ring R
    is-local-commutative-ring-tight-apartness-relation-Commutative-Ring
      a b is-invertible-a+b =
      map-disjunction
        ( backward-implication (inv-iff-apart-zero a))
        ( λ 0#-b →
          backward-implication
            ( inv-iff-apart-zero b)
            ( binary-tr
              ( apart-Tight-Apartness-Relation A)
              ( left-unit-law-add-Commutative-Ring R b)
              ( left-inverse-law-add-Commutative-Ring R b)
              ( preserves-apart-right-add-tight-apartness-relation-Commutative-Ring
                ( b)
                ( zero-R)
                ( neg-R b)
                ( 0#-b))))
        ( extensional-addition-apartness
          ( a)
          ( zero-R)
          ( zero-R)
          ( neg-R b)
          ( apart-is-invertible-diff-tight-apartness-relation-Commutative-Ring
            ( a +R zero-R)
            ( zero-R -R b)
            ( inv-tr
              ( is-invertible-element-Commutative-Ring R)
              ( equational-reasoning
                (a +R zero-R) -R (zero-R -R b)
                ＝ a -R neg-R b
                  by
                    ap-right-subtraction-Commutative-Ring R
                      ( right-unit-law-add-Commutative-Ring R a)
                      ( left-unit-law-add-Commutative-Ring R (neg-R b))
                ＝ a +R b
                  by
                    ap-add-Commutative-Ring R
                      ( refl)
                      ( neg-neg-Commutative-Ring R b))
              ( is-invertible-a+b))))

    is-nontrivial-tight-apartness-relation-Commutative-Ring :
      is-nontrivial-Commutative-Ring R
    is-nontrivial-tight-apartness-relation-Commutative-Ring =
      nonequal-apart-Tight-Apartness-Relation A
        ( zero-R)
        ( one-Commutative-Ring R)
        ( symmetric-Tight-Apartness-Relation A _ _
          ( forward-implication
            ( inv-iff-apart-zero _)
            ( is-invertible-element-one-Commutative-Ring R)))

  local-commutative-ring-tight-apartness-relation-Commutative-Ring :
    Local-Commutative-Ring l1
  local-commutative-ring-tight-apartness-relation-Commutative-Ring =
    ( R ,
      is-local-commutative-ring-tight-apartness-relation-Commutative-Ring)

  abstract
    is-zero-is-not-invertible-tight-apartness-relation-Commutative-Ring :
      (x : type-Commutative-Ring R) →
      ¬ (is-invertible-element-Commutative-Ring R x) →
      x ＝ zero-Commutative-Ring R
    is-zero-is-not-invertible-tight-apartness-relation-Commutative-Ring
      x ¬inv-x =
      is-tight-apartness-relation-Tight-Apartness-Relation A _ _
        ( λ x#0 → ¬inv-x (backward-implication (inv-iff-apart-zero x) x#0))

  heyting-field-tight-apartness-relation-Commutative-Ring : Heyting-Field l1
  heyting-field-tight-apartness-relation-Commutative-Ring =
    ( local-commutative-ring-tight-apartness-relation-Commutative-Ring ,
      is-nontrivial-tight-apartness-relation-Commutative-Ring ,
      is-zero-is-not-invertible-tight-apartness-relation-Commutative-Ring)
```

## External links

- [Heyting field](https://ncatlab.org/nlab/show/Heyting+field) at $n$Lab
