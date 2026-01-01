# Normed algebras over the real numbers

```agda
module commutative-algebra.normed-real-algebras where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.algebras-over-the-real-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.real-vector-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-real-numbers
```

</details>

## Idea

A
{{#concept "normed algebra" WDID=Q1999917 WD="normed algebra" Disambiguation="over the real numbers" Agda=normed-algebra-ℝ}}
over the [real numbers](real-numbers.dedekind-real-numbers.md) is an
[algebra over ℝ](commutative-algebra.algebras-over-the-real-numbers.md) equipped
with a [norm](linear-algebra.normed-real-vector-spaces.md) that is
submultiplicative: for any `x` and `y` in the algebra, `∥xy∥ ≤ ∥x∥ ∥y∥`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (A : algebra-ℝ l1 l2)
  where

  norm-algebra-ℝ : UU (lsuc l1 ⊔ l2)
  norm-algebra-ℝ = norm-ℝ-Vector-Space (vector-space-algebra-ℝ A)

  is-subdistributive-prop-norm-algebra-ℝ : norm-algebra-ℝ → Prop (l1 ⊔ l2)
  is-subdistributive-prop-norm-algebra-ℝ norm =
    let
      V = vector-space-algebra-ℝ A
    in
      Π-Prop
        ( type-algebra-ℝ A)
        ( λ x →
          Π-Prop
            ( type-algebra-ℝ A)
            ( λ y →
              leq-prop-ℝ
                ( map-norm-ℝ-Vector-Space V norm (mul-algebra-ℝ A x y))
                ( ( map-norm-ℝ-Vector-Space V norm x) *ℝ
                  ( map-norm-ℝ-Vector-Space V norm y))))

  is-subdistributive-norm-algebra-ℝ : norm-algebra-ℝ → UU (l1 ⊔ l2)
  is-subdistributive-norm-algebra-ℝ norm =
    type-Prop (is-subdistributive-prop-norm-algebra-ℝ norm)

  subdistributive-norm-algebra-ℝ : UU (lsuc l1 ⊔ l2)
  subdistributive-norm-algebra-ℝ =
    type-subtype is-subdistributive-prop-norm-algebra-ℝ

normed-algebra-ℝ : (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
normed-algebra-ℝ l1 l2 =
  Σ (algebra-ℝ l1 l2) subdistributive-norm-algebra-ℝ
```

## Properties

```agda
module _
  {l1 l2 : Level}
  (A : normed-algebra-ℝ l1 l2)
  where

  algebra-normed-algebra-ℝ : algebra-ℝ l1 l2
  algebra-normed-algebra-ℝ = pr1 A

  vector-space-normed-algebra-ℝ : ℝ-Vector-Space l1 l2
  vector-space-normed-algebra-ℝ =
    vector-space-algebra-ℝ algebra-normed-algebra-ℝ

  norm-normed-algebra-ℝ : norm-ℝ-Vector-Space vector-space-normed-algebra-ℝ
  norm-normed-algebra-ℝ = pr1 (pr2 A)

  normed-vector-space-normed-algebra-ℝ : Normed-ℝ-Vector-Space l1 l2
  normed-vector-space-normed-algebra-ℝ =
    ( vector-space-normed-algebra-ℝ ,
      norm-normed-algebra-ℝ)
```

### The real numbers are a normed algebra over themselves

```agda
real-normed-algebra-ℝ : (l : Level) → normed-algebra-ℝ l (lsuc l)
real-normed-algebra-ℝ l =
  ( real-algebra-ℝ l , norm-abs-ℝ l , λ x y → leq-eq-ℝ (abs-mul-ℝ x y))
```

## See also

- [Normed associative algebras over ℝ](commutative-algebra.normed-associative-real-algebras.md)
