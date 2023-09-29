# Rings of modular arithmetic

```agda
module elementary-number-theory.rings-of-modular-arithmetic where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-integers
open import elementary-number-theory.groups-of-modular-arithmetic
open import elementary-number-theory.integers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.ring-of-integers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.homotopies
open import foundation.identity-types
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.function-types

open import group-theory.generating-elements-groups

open import ring-theory.cyclic-rings
open import ring-theory.integer-multiples-of-elements-rings
open import ring-theory.rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The **standard cyclic rings** `ℤ/n` are the [rings](ring-theory.rings.md) of
[modular arithmetic](elementary-number-theory.modular-arithmetic.md).

The fact that the rings `ℤ/n` are [cyclic](ring-theory.cyclic-rings.md) remains
to be shown.

## Definitions

```agda
ℤ-Mod-Ring : ℕ → Ring lzero
pr1 (ℤ-Mod-Ring n) = ℤ-Mod-Ab n
pr1 (pr1 (pr2 (ℤ-Mod-Ring n))) = mul-ℤ-Mod n
pr2 (pr1 (pr2 (ℤ-Mod-Ring n))) = associative-mul-ℤ-Mod n
pr1 (pr1 (pr2 (pr2 (ℤ-Mod-Ring n)))) = one-ℤ-Mod n
pr1 (pr2 (pr1 (pr2 (pr2 (ℤ-Mod-Ring n))))) = left-unit-law-mul-ℤ-Mod n
pr2 (pr2 (pr1 (pr2 (pr2 (ℤ-Mod-Ring n))))) = right-unit-law-mul-ℤ-Mod n
pr1 (pr2 (pr2 (pr2 (ℤ-Mod-Ring n)))) = left-distributive-mul-add-ℤ-Mod n
pr2 (pr2 (pr2 (pr2 (ℤ-Mod-Ring n)))) = right-distributive-mul-add-ℤ-Mod n

ℤ-Mod-Commutative-Ring : ℕ → Commutative-Ring lzero
pr1 (ℤ-Mod-Commutative-Ring n) = ℤ-Mod-Ring n
pr2 (ℤ-Mod-Commutative-Ring n) = commutative-mul-ℤ-Mod n
```

## Properties

### Rings of modular arithmetic are cyclic

```agda
integer-multiple-one-ℤ-Ring :
  (k : ℤ) →
  ( integer-multiple-Ring (ℤ-Mod-Ring zero-ℕ) k (one-ℤ-Mod zero-ℕ)) ＝
  ( k)
integer-multiple-one-ℤ-Ring (inl zero-ℕ) = refl
integer-multiple-one-ℤ-Ring (inl (succ-ℕ n)) =
  ap pred-ℤ (integer-multiple-one-ℤ-Ring (inl n))
integer-multiple-one-ℤ-Ring (inr (inl star)) = refl
integer-multiple-one-ℤ-Ring (inr (inr zero-ℕ)) = refl
integer-multiple-one-ℤ-Ring (inr (inr (succ-ℕ n))) =
  ap succ-ℤ (integer-multiple-one-ℤ-Ring (inr (inr n)))

is-neg-one-neg-one-ℤ-Mod :
  ( n : ℕ) → (neg-one-Ring (ℤ-Mod-Ring n)) ＝ (neg-one-ℤ-Mod n)
is-neg-one-neg-one-ℤ-Mod zero-ℕ = refl
is-neg-one-neg-one-ℤ-Mod (succ-ℕ n) = is-neg-one-neg-one-Fin n

integer-multiplication-by-one-preserves-succ-ℤ :
  (n : ℕ) (x : ℤ) →
  integer-multiple-Ring (ℤ-Mod-Ring n) (succ-ℤ x) (one-ℤ-Mod n) ＝
  succ-ℤ-Mod n (integer-multiple-Ring (ℤ-Mod-Ring n) x (one-ℤ-Mod n))
integer-multiplication-by-one-preserves-succ-ℤ n x =
  ( integer-multiple-succ-Ring (ℤ-Mod-Ring n) x (one-ℤ-Mod n)) ∙
  ( inv
    ( is-left-add-one-succ-ℤ-Mod'
      ( n)
      ( integer-multiple-Ring (ℤ-Mod-Ring n) x (one-ℤ-Mod n))))

integer-multiplication-by-one-preserves-pred-ℤ :
  (n : ℕ) (x : ℤ) →
  integer-multiple-Ring (ℤ-Mod-Ring n) (pred-ℤ x) (one-ℤ-Mod n) ＝
  pred-ℤ-Mod n (integer-multiple-Ring (ℤ-Mod-Ring n) x (one-ℤ-Mod n))
integer-multiplication-by-one-preserves-pred-ℤ n x =
  ( ap
    ( λ k → integer-multiple-Ring (ℤ-Mod-Ring n) k (one-ℤ-Mod n))
    ( is-right-add-neg-one-pred-ℤ x)) ∙
  ( distributive-integer-multiple-add-Ring
    ( ℤ-Mod-Ring n)
    ( one-ℤ-Mod n)
    ( x)
    ( neg-one-ℤ)) ∙
  ( ap
    ( λ k →
      add-ℤ-Mod n
      ( integer-multiple-Ring (ℤ-Mod-Ring n) x (one-ℤ-Mod n))
      ( k))
    ( integer-multiple-neg-one-Ring (ℤ-Mod-Ring n) (one-ℤ-Mod n))) ∙
  ( ap
    ( λ k →
      add-ℤ-Mod n
      ( integer-multiple-Ring (ℤ-Mod-Ring n) x (one-ℤ-Mod n))
      ( k))
    ( is-neg-one-neg-one-ℤ-Mod n)) ∙
    ( inv
      ( is-left-add-neg-one-pred-ℤ-Mod'
        ( n)
        ( integer-multiple-Ring (ℤ-Mod-Ring n) x (one-ℤ-Mod n))))

compute-integer-multiple-one-ℤ-Mod :
  ( n : ℕ) →
  ( λ k → integer-multiple-Ring (ℤ-Mod-Ring n) k (one-ℤ-Mod n)) ~
  ( mod-ℤ n)
compute-integer-multiple-one-ℤ-Mod zero-ℕ x = integer-multiple-one-ℤ-Ring x
compute-integer-multiple-one-ℤ-Mod (succ-ℕ n) (inl zero-ℕ) =
  ( integer-multiple-neg-one-Ring
    ( ℤ-Mod-Ring (succ-ℕ n))
    ( one-ℤ-Mod (succ-ℕ n))) ∙
  ( is-neg-one-neg-one-ℤ-Mod (succ-ℕ n)) ∙
  ( inv (mod-neg-one-ℤ (succ-ℕ n)))
compute-integer-multiple-one-ℤ-Mod (succ-ℕ n) (inl (succ-ℕ x)) =
  ( integer-multiplication-by-one-preserves-pred-ℤ
    ( succ-ℕ n)
    ( inl x)) ∙
  ( ap
    ( pred-ℤ-Mod (succ-ℕ n))
    ( compute-integer-multiple-one-ℤ-Mod (succ-ℕ n) (inl x))) ∙
  (inv (preserves-predecessor-mod-ℤ (succ-ℕ n) (inl x)))
compute-integer-multiple-one-ℤ-Mod (succ-ℕ n) (inr (inl star)) = refl
compute-integer-multiple-one-ℤ-Mod (succ-ℕ n) (inr (inr zero-ℕ)) =
  ( integer-multiple-one-Ring
    ( ℤ-Mod-Ring (succ-ℕ n))
    ( one-ℤ-Mod (succ-ℕ n))) ∙
  ( inv (mod-one-ℤ (succ-ℕ n)))
compute-integer-multiple-one-ℤ-Mod (succ-ℕ n) (inr (inr (succ-ℕ x))) =
  ( integer-multiplication-by-one-preserves-succ-ℤ
    ( succ-ℕ n)
    ( inr (inr x))) ∙
  ( ap
    ( succ-ℤ-Mod (succ-ℕ n))
    ( compute-integer-multiple-one-ℤ-Mod (succ-ℕ n) (inr (inr x)))) ∙
  (inv (preserves-successor-mod-ℤ (succ-ℕ n) (inr (inr x))))

is-surjective-hom-element-one-ℤ-Mod-Ring :
  ( n : ℕ) → is-surjective-hom-element-Group (ℤ-Mod-Group n) (one-ℤ-Mod n)
is-surjective-hom-element-one-ℤ-Mod-Ring n =
  is-surjective-htpy
    ( compute-integer-multiple-one-ℤ-Mod n)
    ( is-surjective-mod-ℤ n)

is-generating-element-one-ℤ-Mod-Ring :
  ( n : ℕ) → is-generating-element-Group (ℤ-Mod-Group n) (one-ℤ-Mod n)
is-generating-element-one-ℤ-Mod-Ring n =
  is-generating-element-is-surjective-hom-element-Group
    ( ℤ-Mod-Group n)
    ( one-ℤ-Mod n)
    ( is-surjective-hom-element-one-ℤ-Mod-Ring n)

is-cyclic-ℤ-Mod-Ring :
  ( n : ℕ) → is-cyclic-Ring (ℤ-Mod-Ring n)
is-cyclic-ℤ-Mod-Ring n =
  intro-∃
    ( one-ℤ-Mod n)
    ( is-generating-element-one-ℤ-Mod-Ring n)
```
