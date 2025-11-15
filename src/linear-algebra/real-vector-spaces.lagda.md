# Real vector spaces

```agda
module linear-algebra.real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.vector-spaces

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.local-ring-of-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

A
{{#concept "real vector space" WD="real vector space" WDID=Q46996054 Agda=ℝ-Vector-Space}}
is a [vector space](linear-algebra.vector-spaces.md) over the
[local commutative ring of real numbers](real-numbers.local-ring-of-real-numbers.md).

## Definition

```agda
ℝ-Vector-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
ℝ-Vector-Space l1 l2 = Vector-Space l2 (local-commutative-ring-ℝ l1)
```

## Properties

```agda
module _
  {l1 l2 : Level} (V : ℝ-Vector-Space l1 l2)
  where

  ab-ℝ-Vector-Space : Ab l2
  ab-ℝ-Vector-Space = ab-Vector-Space (local-commutative-ring-ℝ l1) V

  set-ℝ-Vector-Space : Set l2
  set-ℝ-Vector-Space = set-Ab ab-ℝ-Vector-Space

  type-ℝ-Vector-Space : UU l2
  type-ℝ-Vector-Space = type-Ab ab-ℝ-Vector-Space

  add-ℝ-Vector-Space :
    type-ℝ-Vector-Space → type-ℝ-Vector-Space → type-ℝ-Vector-Space
  add-ℝ-Vector-Space = add-Ab ab-ℝ-Vector-Space

  zero-ℝ-Vector-Space : type-ℝ-Vector-Space
  zero-ℝ-Vector-Space = zero-Ab ab-ℝ-Vector-Space

  neg-ℝ-Vector-Space : type-ℝ-Vector-Space → type-ℝ-Vector-Space
  neg-ℝ-Vector-Space = neg-Ab ab-ℝ-Vector-Space

  mul-ℝ-Vector-Space : ℝ l1 → type-ℝ-Vector-Space → type-ℝ-Vector-Space
  mul-ℝ-Vector-Space = mul-Vector-Space (local-commutative-ring-ℝ l1) V

  associative-add-ℝ-Vector-Space :
    (v w x : type-ℝ-Vector-Space) →
    add-ℝ-Vector-Space (add-ℝ-Vector-Space v w) x ＝
    add-ℝ-Vector-Space v (add-ℝ-Vector-Space w x)
  associative-add-ℝ-Vector-Space = associative-add-Ab ab-ℝ-Vector-Space

  left-unit-law-add-ℝ-Vector-Space :
    (v : type-ℝ-Vector-Space) → add-ℝ-Vector-Space zero-ℝ-Vector-Space v ＝ v
  left-unit-law-add-ℝ-Vector-Space = left-unit-law-add-Ab ab-ℝ-Vector-Space

  right-unit-law-add-ℝ-Vector-Space :
    (v : type-ℝ-Vector-Space) → add-ℝ-Vector-Space v zero-ℝ-Vector-Space ＝ v
  right-unit-law-add-ℝ-Vector-Space = right-unit-law-add-Ab ab-ℝ-Vector-Space

  left-inverse-law-add-ℝ-Vector-Space :
    (v : type-ℝ-Vector-Space) →
    add-ℝ-Vector-Space (neg-ℝ-Vector-Space v) v ＝ zero-ℝ-Vector-Space
  left-inverse-law-add-ℝ-Vector-Space =
    left-inverse-law-add-Ab ab-ℝ-Vector-Space

  right-inverse-law-add-ℝ-Vector-Space :
    (v : type-ℝ-Vector-Space) →
    add-ℝ-Vector-Space v (neg-ℝ-Vector-Space v) ＝ zero-ℝ-Vector-Space
  right-inverse-law-add-ℝ-Vector-Space =
    right-inverse-law-add-Ab ab-ℝ-Vector-Space

  commutative-add-ℝ-Vector-Space :
    (v w : type-ℝ-Vector-Space) →
    add-ℝ-Vector-Space v w ＝ add-ℝ-Vector-Space w v
  commutative-add-ℝ-Vector-Space = commutative-add-Ab ab-ℝ-Vector-Space

  left-unit-law-mul-ℝ-Vector-Space :
    (v : type-ℝ-Vector-Space) →
    mul-ℝ-Vector-Space (raise-ℝ l1 one-ℝ) v ＝ v
  left-unit-law-mul-ℝ-Vector-Space =
    left-unit-law-mul-Vector-Space (local-commutative-ring-ℝ l1) V

  left-distributive-mul-add-ℝ-Vector-Space :
    (r : ℝ l1) (v w : type-ℝ-Vector-Space) →
    mul-ℝ-Vector-Space r (add-ℝ-Vector-Space v w) ＝
    add-ℝ-Vector-Space (mul-ℝ-Vector-Space r v) (mul-ℝ-Vector-Space r w)
  left-distributive-mul-add-ℝ-Vector-Space =
    left-distributive-mul-add-Vector-Space (local-commutative-ring-ℝ l1) V

  right-distributive-mul-add-ℝ-Vector-Space :
    (r s : ℝ l1) (v : type-ℝ-Vector-Space) →
    mul-ℝ-Vector-Space (r +ℝ s) v ＝
    add-ℝ-Vector-Space (mul-ℝ-Vector-Space r v) (mul-ℝ-Vector-Space s v)
  right-distributive-mul-add-ℝ-Vector-Space =
    right-distributive-mul-add-Vector-Space (local-commutative-ring-ℝ l1) V

  associative-mul-ℝ-Vector-Space :
    (r s : ℝ l1) (v : type-ℝ-Vector-Space) →
    mul-ℝ-Vector-Space (r *ℝ s) v ＝
    mul-ℝ-Vector-Space r (mul-ℝ-Vector-Space s v)
  associative-mul-ℝ-Vector-Space =
    associative-mul-Vector-Space (local-commutative-ring-ℝ l1) V

  left-zero-law-mul-ℝ-Vector-Space :
    (v : type-ℝ-Vector-Space) →
    mul-ℝ-Vector-Space (raise-ℝ l1 zero-ℝ) v ＝ zero-ℝ-Vector-Space
  left-zero-law-mul-ℝ-Vector-Space =
    left-zero-law-mul-Vector-Space (local-commutative-ring-ℝ l1) V

  right-zero-law-mul-ℝ-Vector-Space :
    (r : ℝ l1) →
    mul-ℝ-Vector-Space r zero-ℝ-Vector-Space ＝ zero-ℝ-Vector-Space
  right-zero-law-mul-ℝ-Vector-Space =
    right-zero-law-mul-Vector-Space (local-commutative-ring-ℝ l1) V

  left-negative-law-mul-ℝ-Vector-Space :
    (r : ℝ l1) (v : type-ℝ-Vector-Space) →
    mul-ℝ-Vector-Space (neg-ℝ r) v ＝
    neg-ℝ-Vector-Space (mul-ℝ-Vector-Space r v)
  left-negative-law-mul-ℝ-Vector-Space =
    left-negative-law-mul-Vector-Space (local-commutative-ring-ℝ l1) V

  right-negative-law-mul-ℝ-Vector-Space :
    (r : ℝ l1) (v : type-ℝ-Vector-Space) →
    mul-ℝ-Vector-Space r (neg-ℝ-Vector-Space v) ＝
    neg-ℝ-Vector-Space (mul-ℝ-Vector-Space r v)
  right-negative-law-mul-ℝ-Vector-Space =
    right-negative-law-mul-Vector-Space (local-commutative-ring-ℝ l1) V

  mul-neg-one-ℝ-Vector-Space :
    (v : type-ℝ-Vector-Space) →
    mul-ℝ-Vector-Space (neg-ℝ (raise-ℝ l1 one-ℝ)) v ＝ neg-ℝ-Vector-Space v
  mul-neg-one-ℝ-Vector-Space =
    mul-neg-one-Vector-Space (local-commutative-ring-ℝ l1) V
```
