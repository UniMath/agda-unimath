# Complex vector spaces

```agda
module linear-algebra.complex-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.addition-complex-numbers
open import complex-numbers.complex-numbers
open import complex-numbers.field-of-complex-numbers
open import complex-numbers.multiplication-complex-numbers
open import complex-numbers.raising-universe-levels-complex-numbers

open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.real-vector-spaces
open import linear-algebra.vector-spaces

open import real-numbers.field-of-real-numbers
```

</details>

## Idea

A
{{#concept "complex vector space" WD="complex vector space" WDID=Q5156614 Agda=ℂ-Vector-Space}}
is a [vector space](linear-algebra.vector-spaces.md) over the
[Heyting field of complex numbers](complex-numbers.field-of-complex-numbers.md).

## Definition

```agda
ℂ-Vector-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
ℂ-Vector-Space l1 l2 = Vector-Space l2 (heyting-field-ℂ l1)
```

## Properties

```agda
module _
  {l1 l2 : Level} (V : ℂ-Vector-Space l1 l2)
  where

  ab-ℂ-Vector-Space : Ab l2
  ab-ℂ-Vector-Space = ab-Vector-Space (heyting-field-ℂ l1) V

  set-ℂ-Vector-Space : Set l2
  set-ℂ-Vector-Space = set-Ab ab-ℂ-Vector-Space

  type-ℂ-Vector-Space : UU l2
  type-ℂ-Vector-Space = type-Ab ab-ℂ-Vector-Space

  add-ℂ-Vector-Space :
    type-ℂ-Vector-Space → type-ℂ-Vector-Space → type-ℂ-Vector-Space
  add-ℂ-Vector-Space = add-Ab ab-ℂ-Vector-Space

  zero-ℂ-Vector-Space : type-ℂ-Vector-Space
  zero-ℂ-Vector-Space = zero-Ab ab-ℂ-Vector-Space

  neg-ℂ-Vector-Space : type-ℂ-Vector-Space → type-ℂ-Vector-Space
  neg-ℂ-Vector-Space = neg-Ab ab-ℂ-Vector-Space

  mul-ℂ-Vector-Space : ℂ l1 → type-ℂ-Vector-Space → type-ℂ-Vector-Space
  mul-ℂ-Vector-Space = mul-Vector-Space (heyting-field-ℂ l1) V

  associative-add-ℂ-Vector-Space :
    (v w x : type-ℂ-Vector-Space) →
    add-ℂ-Vector-Space (add-ℂ-Vector-Space v w) x ＝
    add-ℂ-Vector-Space v (add-ℂ-Vector-Space w x)
  associative-add-ℂ-Vector-Space = associative-add-Ab ab-ℂ-Vector-Space

  left-unit-law-add-ℂ-Vector-Space :
    (v : type-ℂ-Vector-Space) → add-ℂ-Vector-Space zero-ℂ-Vector-Space v ＝ v
  left-unit-law-add-ℂ-Vector-Space = left-unit-law-add-Ab ab-ℂ-Vector-Space

  right-unit-law-add-ℂ-Vector-Space :
    (v : type-ℂ-Vector-Space) → add-ℂ-Vector-Space v zero-ℂ-Vector-Space ＝ v
  right-unit-law-add-ℂ-Vector-Space = right-unit-law-add-Ab ab-ℂ-Vector-Space

  left-inverse-law-add-ℂ-Vector-Space :
    (v : type-ℂ-Vector-Space) →
    add-ℂ-Vector-Space (neg-ℂ-Vector-Space v) v ＝ zero-ℂ-Vector-Space
  left-inverse-law-add-ℂ-Vector-Space =
    left-inverse-law-add-Ab ab-ℂ-Vector-Space

  right-inverse-law-add-ℂ-Vector-Space :
    (v : type-ℂ-Vector-Space) →
    add-ℂ-Vector-Space v (neg-ℂ-Vector-Space v) ＝ zero-ℂ-Vector-Space
  right-inverse-law-add-ℂ-Vector-Space =
    right-inverse-law-add-Ab ab-ℂ-Vector-Space

  commutative-add-ℂ-Vector-Space :
    (v w : type-ℂ-Vector-Space) →
    add-ℂ-Vector-Space v w ＝ add-ℂ-Vector-Space w v
  commutative-add-ℂ-Vector-Space = commutative-add-Ab ab-ℂ-Vector-Space

  left-unit-law-mul-ℂ-Vector-Space :
    (v : type-ℂ-Vector-Space) →
    mul-ℂ-Vector-Space (raise-ℂ l1 one-ℂ) v ＝ v
  left-unit-law-mul-ℂ-Vector-Space =
    left-unit-law-mul-Vector-Space (heyting-field-ℂ l1) V

  left-distributive-mul-add-ℂ-Vector-Space :
    (r : ℂ l1) (v w : type-ℂ-Vector-Space) →
    mul-ℂ-Vector-Space r (add-ℂ-Vector-Space v w) ＝
    add-ℂ-Vector-Space (mul-ℂ-Vector-Space r v) (mul-ℂ-Vector-Space r w)
  left-distributive-mul-add-ℂ-Vector-Space =
    left-distributive-mul-add-Vector-Space (heyting-field-ℂ l1) V

  right-distributive-mul-add-ℂ-Vector-Space :
    (r s : ℂ l1) (v : type-ℂ-Vector-Space) →
    mul-ℂ-Vector-Space (r +ℂ s) v ＝
    add-ℂ-Vector-Space (mul-ℂ-Vector-Space r v) (mul-ℂ-Vector-Space s v)
  right-distributive-mul-add-ℂ-Vector-Space =
    right-distributive-mul-add-Vector-Space (heyting-field-ℂ l1) V

  associative-mul-ℂ-Vector-Space :
    (r s : ℂ l1) (v : type-ℂ-Vector-Space) →
    mul-ℂ-Vector-Space (r *ℂ s) v ＝
    mul-ℂ-Vector-Space r (mul-ℂ-Vector-Space s v)
  associative-mul-ℂ-Vector-Space =
    associative-mul-Vector-Space (heyting-field-ℂ l1) V

  left-zero-law-mul-ℂ-Vector-Space :
    (v : type-ℂ-Vector-Space) →
    mul-ℂ-Vector-Space (raise-ℂ l1 zero-ℂ) v ＝ zero-ℂ-Vector-Space
  left-zero-law-mul-ℂ-Vector-Space =
    left-zero-law-mul-Vector-Space (heyting-field-ℂ l1) V

  right-zero-law-mul-ℂ-Vector-Space :
    (r : ℂ l1) →
    mul-ℂ-Vector-Space r zero-ℂ-Vector-Space ＝ zero-ℂ-Vector-Space
  right-zero-law-mul-ℂ-Vector-Space =
    right-zero-law-mul-Vector-Space (heyting-field-ℂ l1) V

  left-negative-law-mul-ℂ-Vector-Space :
    (r : ℂ l1) (v : type-ℂ-Vector-Space) →
    mul-ℂ-Vector-Space (neg-ℂ r) v ＝
    neg-ℂ-Vector-Space (mul-ℂ-Vector-Space r v)
  left-negative-law-mul-ℂ-Vector-Space =
    left-negative-law-mul-Vector-Space (heyting-field-ℂ l1) V

  right-negative-law-mul-ℂ-Vector-Space :
    (r : ℂ l1) (v : type-ℂ-Vector-Space) →
    mul-ℂ-Vector-Space r (neg-ℂ-Vector-Space v) ＝
    neg-ℂ-Vector-Space (mul-ℂ-Vector-Space r v)
  right-negative-law-mul-ℂ-Vector-Space =
    right-negative-law-mul-Vector-Space (heyting-field-ℂ l1) V

  mul-neg-one-ℂ-Vector-Space :
    (v : type-ℂ-Vector-Space) →
    mul-ℂ-Vector-Space (neg-ℂ (raise-ℂ l1 one-ℂ)) v ＝ neg-ℂ-Vector-Space v
  mul-neg-one-ℂ-Vector-Space =
    mul-neg-one-Vector-Space (heyting-field-ℂ l1) V
```

### The complex numbers are a complex vector space

```agda
complex-vector-space-ℂ : (l : Level) → ℂ-Vector-Space l (lsuc l)
complex-vector-space-ℂ l =
  vector-space-heyting-field-Heyting-Field
    ( heyting-field-ℂ l)
```

### Every complex vector space is a real vector space

```agda
real-vector-space-ℂ-Vector-Space :
  {l1 l2 : Level} → ℂ-Vector-Space l1 l2 → ℝ-Vector-Space l1 l2
real-vector-space-ℂ-Vector-Space {l1} =
  vector-space-hom-Vector-Space
    ( heyting-field-ℝ l1)
    ( heyting-field-ℂ l1)
    ( hom-heyting-field-ℝ-ℂ l1)
```
