# The standard cyclic rings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.standard-cyclic-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings funext univalence truncations

open import elementary-number-theory.addition-integers funext univalence truncations
open import elementary-number-theory.integers
open import elementary-number-theory.modular-arithmetic funext univalence truncations
open import elementary-number-theory.modular-arithmetic-standard-finite-types funext univalence truncations
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.ring-of-integers funext univalence truncations
open import elementary-number-theory.standard-cyclic-groups funext univalence truncations

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.existential-quantification funext univalence truncations
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.surjective-maps funext univalence truncations
open import foundation.universe-levels

open import group-theory.cyclic-groups funext univalence truncations
open import group-theory.generating-elements-groups funext univalence truncations

open import ring-theory.cyclic-rings funext univalence truncations
open import ring-theory.integer-multiples-of-elements-rings funext univalence truncations
open import ring-theory.rings funext univalence truncations
```

</details>

## Idea

The **standard cyclic rings** `ℤ/n` are the [rings](ring-theory.rings.md) of
[integers](elementary-number-theory.integers.md)
[modulo `n`](elementary-number-theory.modular-arithmetic.md).

## Definitions

### The standard cyclic rings

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

### Integer multiplication in the standard cyclic rings

```agda
integer-multiple-ℤ-Mod :
  (n : ℕ) → ℤ → ℤ-Mod n → ℤ-Mod n
integer-multiple-ℤ-Mod n k x = integer-multiple-Ring (ℤ-Mod-Ring n) k x
```

## Properties

### The negative-one element of the ring `ℤ/n` coincides with the element `neg-one-ℤ-Mod n`

```agda
is-neg-one-neg-one-ℤ-Mod :
  ( n : ℕ) → neg-one-Ring (ℤ-Mod-Ring n) ＝ neg-one-ℤ-Mod n
is-neg-one-neg-one-ℤ-Mod zero-ℕ = refl
is-neg-one-neg-one-ℤ-Mod (succ-ℕ n) = is-neg-one-neg-one-Fin n
```

### The integer multiple `k · 1` is equal to `[k] : ℤ-Mod n`

```agda
integer-multiplication-by-one-preserves-succ-ℤ :
  (n : ℕ) (x : ℤ) →
  integer-multiple-ℤ-Mod n (succ-ℤ x) (one-ℤ-Mod n) ＝
  succ-ℤ-Mod n (integer-multiple-ℤ-Mod n x (one-ℤ-Mod n))
integer-multiplication-by-one-preserves-succ-ℤ n x =
  ( integer-multiple-succ-Ring (ℤ-Mod-Ring n) x (one-ℤ-Mod n)) ∙
  ( inv
    ( is-left-add-one-succ-ℤ-Mod'
      ( n)
      ( integer-multiple-Ring (ℤ-Mod-Ring n) x (one-ℤ-Mod n))))

integer-multiplication-by-one-preserves-pred-ℤ :
  (n : ℕ) (x : ℤ) →
  integer-multiple-ℤ-Mod n (pred-ℤ x) (one-ℤ-Mod n) ＝
  pred-ℤ-Mod n (integer-multiple-ℤ-Mod n x (one-ℤ-Mod n))
integer-multiplication-by-one-preserves-pred-ℤ n x =
  ( ap
    ( λ k → integer-multiple-ℤ-Mod n k (one-ℤ-Mod n))
    ( is-right-add-neg-one-pred-ℤ x)) ∙
  ( distributive-integer-multiple-add-Ring
    ( ℤ-Mod-Ring n)
    ( one-ℤ-Mod n)
    ( x)
    ( neg-one-ℤ)) ∙
  ( ap
    ( λ k →
      add-ℤ-Mod n
      ( integer-multiple-ℤ-Mod n x (one-ℤ-Mod n))
      ( k))
    ( integer-multiple-neg-one-Ring (ℤ-Mod-Ring n) (one-ℤ-Mod n))) ∙
  ( ap
    ( λ k →
      add-ℤ-Mod n
      ( integer-multiple-ℤ-Mod n x (one-ℤ-Mod n))
      ( k))
    ( is-neg-one-neg-one-ℤ-Mod n)) ∙
    ( inv
      ( is-left-add-neg-one-pred-ℤ-Mod'
        ( n)
        ( integer-multiple-ℤ-Mod n x (one-ℤ-Mod n))))

compute-integer-multiple-one-ℤ-Mod :
  ( n : ℕ) → (λ k → integer-multiple-ℤ-Mod n k (one-ℤ-Mod n)) ~ mod-ℤ n
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
  ( inv (preserves-predecessor-mod-ℤ (succ-ℕ n) (inl x)))
compute-integer-multiple-one-ℤ-Mod (succ-ℕ n) (inr (inl _)) = refl
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
  ( inv (preserves-successor-mod-ℤ (succ-ℕ n) (inr (inr x))))
```

### The standard cyclic rings are cyclic

```agda
is-surjective-hom-element-one-ℤ-Mod :
  ( n : ℕ) → is-surjective-hom-element-Group (ℤ-Mod-Group n) (one-ℤ-Mod n)
is-surjective-hom-element-one-ℤ-Mod n =
  is-surjective-htpy
    ( compute-integer-multiple-one-ℤ-Mod n)
    ( is-surjective-mod-ℤ n)

is-generating-element-one-ℤ-Mod :
  ( n : ℕ) → is-generating-element-Group (ℤ-Mod-Group n) (one-ℤ-Mod n)
is-generating-element-one-ℤ-Mod n =
  is-generating-element-is-surjective-hom-element-Group
    ( ℤ-Mod-Group n)
    ( one-ℤ-Mod n)
    ( is-surjective-hom-element-one-ℤ-Mod n)

is-cyclic-ℤ-Mod-Group :
  ( n : ℕ) → is-cyclic-Group (ℤ-Mod-Group n)
is-cyclic-ℤ-Mod-Group n =
  intro-exists
    ( one-ℤ-Mod n)
    ( is-generating-element-one-ℤ-Mod n)

is-cyclic-ℤ-Mod-Ring :
  ( n : ℕ) → is-cyclic-Ring (ℤ-Mod-Ring n)
is-cyclic-ℤ-Mod-Ring =
  is-cyclic-ℤ-Mod-Group
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
