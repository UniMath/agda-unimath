# The ring of integers

```agda
module elementary-number-theory.ring-of-integers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-integers
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-integers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.free-groups-with-one-generator
open import group-theory.homomorphisms-groups

open import ring-theory.homomorphisms-rings
open import ring-theory.initial-rings
open import ring-theory.integer-multiples-of-elements-rings
open import ring-theory.rings
open import ring-theory.trivial-rings
```

</details>

## Idea

The type of [integers](elementary-number-theory.integers.md) equipped with
[addition](elementary-number-theory.addition-integers.md) and
[multiplication](elementary-number-theory.multiplication-integers.md) is a
[commutative ring](commutative-algebra.commutative-rings.md).

The {{#concept "ring of integers" Agda=ℤ-Ring}} is the **initial**
[ring](ring-theory.rings.md): for any ring `R`, there's a unique
[ring homomorphism](ring-theory.homomorphisms-rings.md) from `ℤ` to `R`, i.e.,
the type of ring homomorphisms `hom-Ring ℤ-Ring R` is
[contractible](foundation.contractible-types.md).

## Definition

```agda
ℤ-Ring : Ring lzero
pr1 ℤ-Ring = ℤ-Ab
pr1 (pr1 (pr2 ℤ-Ring)) = mul-ℤ
pr2 (pr1 (pr2 ℤ-Ring)) = associative-mul-ℤ
pr1 (pr1 (pr2 (pr2 ℤ-Ring))) = one-ℤ
pr1 (pr2 (pr1 (pr2 (pr2 ℤ-Ring)))) = left-unit-law-mul-ℤ
pr2 (pr2 (pr1 (pr2 (pr2 ℤ-Ring)))) = right-unit-law-mul-ℤ
pr1 (pr2 (pr2 (pr2 ℤ-Ring))) = left-distributive-mul-add-ℤ
pr2 (pr2 (pr2 (pr2 ℤ-Ring))) = right-distributive-mul-add-ℤ

ℤ-Commutative-Ring : Commutative-Ring lzero
pr1 ℤ-Commutative-Ring = ℤ-Ring
pr2 ℤ-Commutative-Ring = commutative-mul-ℤ
```

## Properties

### The ring of integers is nontrivial

```agda
is-nontrivial-ℤ-Ring : is-nontrivial-Ring ℤ-Ring
is-nontrivial-ℤ-Ring H = is-nonzero-one-ℤ (inv H)
```

### The integer multiples in `ℤ-Ring` coincide with multiplication in `ℤ`

```agda
abstract
  integer-multiple-one-ℤ-Ring :
    (k : ℤ) → integer-multiple-Ring ℤ-Ring k one-ℤ ＝ k
  integer-multiple-one-ℤ-Ring (inl zero-ℕ) = refl
  integer-multiple-one-ℤ-Ring (inl (succ-ℕ n)) =
    ap pred-ℤ (integer-multiple-one-ℤ-Ring (inl n))
  integer-multiple-one-ℤ-Ring (inr (inl _)) = refl
  integer-multiple-one-ℤ-Ring (inr (inr zero-ℕ)) = refl
  integer-multiple-one-ℤ-Ring (inr (inr (succ-ℕ n))) =
    ap succ-ℤ (integer-multiple-one-ℤ-Ring (inr (inr n)))

  compute-integer-multiple-ℤ-Ring :
    (k l : ℤ) → integer-multiple-Ring ℤ-Ring k l ＝ mul-ℤ k l
  compute-integer-multiple-ℤ-Ring (inl zero-ℕ) l =
    ( integer-multiple-neg-one-Ring ℤ-Ring l) ∙
    ( inv (left-neg-unit-law-mul-ℤ l))
  compute-integer-multiple-ℤ-Ring (inl (succ-ℕ k)) l =
    ( integer-multiple-pred-Ring ℤ-Ring (inl k) l) ∙
    ( ap
      ( λ t → right-subtraction-Ring ℤ-Ring t l)
      ( compute-integer-multiple-ℤ-Ring (inl k) l)) ∙
    ( commutative-add-ℤ (mul-ℤ (inl k) l) (neg-ℤ l)) ∙
    ( inv (left-predecessor-law-mul-ℤ (inl k) l))
  compute-integer-multiple-ℤ-Ring (inr (inl _)) l =
    ( integer-multiple-zero-Ring ℤ-Ring l) ∙
    ( inv (left-zero-law-mul-ℤ l))
  compute-integer-multiple-ℤ-Ring (inr (inr zero-ℕ)) l =
    ( integer-multiple-one-Ring ℤ-Ring l) ∙
    ( inv (left-unit-law-mul-ℤ l))
  compute-integer-multiple-ℤ-Ring (inr (inr (succ-ℕ k))) l =
    ( integer-multiple-succ-Ring ℤ-Ring (inr (inr k)) l) ∙
    ( ap (add-ℤ' l) (compute-integer-multiple-ℤ-Ring (inr (inr k)) l)) ∙
    ( commutative-add-ℤ _ l) ∙
    ( inv (left-successor-law-mul-ℤ (inr (inr k)) l))

  is-integer-multiple-ℤ :
    (k : ℤ) → integer-multiple-Ring ℤ-Ring k one-ℤ ＝ k
  is-integer-multiple-ℤ k =
    ( compute-integer-multiple-ℤ-Ring k one-ℤ) ∙
    ( right-unit-law-mul-ℤ k)
```

### The ring of integers is the initial ring

#### The homomorphism from `ℤ` to a ring

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  hom-group-initial-hom-Ring : hom-Group ℤ-Group (group-Ring R)
  hom-group-initial-hom-Ring = hom-element-Group (group-Ring R) (one-Ring R)

  map-initial-hom-Ring : ℤ → type-Ring R
  map-initial-hom-Ring =
    map-hom-Group ℤ-Group (group-Ring R) hom-group-initial-hom-Ring

  abstract
    preserves-add-initial-hom-Ring :
      (k l : ℤ) →
      map-initial-hom-Ring (add-ℤ k l) ＝
      add-Ring R (map-initial-hom-Ring k) (map-initial-hom-Ring l)
    preserves-add-initial-hom-Ring k l =
      preserves-mul-hom-Group
        ( ℤ-Group)
        ( group-Ring R)
        ( hom-group-initial-hom-Ring)
        { k}
        { l}

    preserves-one-initial-hom-Ring : map-initial-hom-Ring one-ℤ ＝ one-Ring R
    preserves-one-initial-hom-Ring = integer-multiple-one-Ring R (one-Ring R)

    preserves-mul-initial-hom-Ring :
      (k l : ℤ) →
      map-initial-hom-Ring (mul-ℤ k l) ＝
      mul-Ring R (map-initial-hom-Ring k) (map-initial-hom-Ring l)
    preserves-mul-initial-hom-Ring k l =
      ( ap map-initial-hom-Ring (commutative-mul-ℤ k l)) ∙
      ( integer-multiple-mul-Ring R l k (one-Ring R)) ∙
      ( ap (integer-multiple-Ring R l) (inv (right-unit-law-mul-Ring R _))) ∙
      ( inv (right-integer-multiple-law-mul-Ring R l _ _))

  initial-hom-Ring : hom-Ring ℤ-Ring R
  pr1 initial-hom-Ring = hom-group-initial-hom-Ring
  pr1 (pr2 initial-hom-Ring) {x} {y} = preserves-mul-initial-hom-Ring x y
  pr2 (pr2 initial-hom-Ring) = preserves-one-initial-hom-Ring
```

#### Any ring homomorphism from `ℤ` to `R` is equal to the homomorphism `initial-hom-Ring`

```agda
module _
  {l : Level} (R : Ring l)
  where

  abstract
    htpy-initial-hom-Ring :
      (f : hom-Ring ℤ-Ring R) → htpy-hom-Ring ℤ-Ring R (initial-hom-Ring R) f
    htpy-initial-hom-Ring f k =
      ( inv
        ( ( preserves-integer-multiples-hom-Ring ℤ-Ring R f k one-ℤ) ∙
          ( ap
            ( integer-multiple-Ring R k)
            ( preserves-one-hom-Ring ℤ-Ring R f)))) ∙
      ( ap (map-hom-Ring ℤ-Ring R f) (is-integer-multiple-ℤ k))

    contraction-initial-hom-Ring :
      (f : hom-Ring ℤ-Ring R) → initial-hom-Ring R ＝ f
    contraction-initial-hom-Ring f =
      eq-htpy-hom-Ring ℤ-Ring R (initial-hom-Ring R) f (htpy-initial-hom-Ring f)
```

#### The ring of integers is the initial ring

```agda
is-initial-ℤ-Ring : is-initial-Ring ℤ-Ring
pr1 (is-initial-ℤ-Ring S) = initial-hom-Ring S
pr2 (is-initial-ℤ-Ring S) f = contraction-initial-hom-Ring S f
```

### The image of `ℤ` in a ring is commutative

```agda
module _
  {l : Level} (R : Ring l)
  where

  abstract
    is-commutative-map-initial-hom-Ring :
      (p q : ℤ) →
      mul-Ring
        ( R)
        ( map-initial-hom-Ring R p)
        ( map-initial-hom-Ring R q) ＝
      mul-Ring
        ( R)
        ( map-initial-hom-Ring R q)
        ( map-initial-hom-Ring R p)
    is-commutative-map-initial-hom-Ring p q =
      ( inv (preserves-mul-initial-hom-Ring R p q)) ∙
      ( ap (map-initial-hom-Ring R) (commutative-mul-ℤ p q)) ∙
      ( preserves-mul-initial-hom-Ring R q p)
```
