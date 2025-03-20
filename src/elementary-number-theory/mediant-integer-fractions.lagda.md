# The mediant fraction of two integer fractions

```agda
open import foundation.function-extensionality-axiom

module
  elementary-number-theory.mediant-integer-fractions
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers funext
open import elementary-number-theory.addition-positive-and-negative-integers funext
open import elementary-number-theory.cross-multiplication-difference-integer-fractions funext
open import elementary-number-theory.difference-integers funext
open import elementary-number-theory.integer-fractions funext
open import elementary-number-theory.multiplication-integers funext

open import foundation.dependent-pair-types
open import foundation.identity-types funext
```

</details>

## Idea

The
{{#concept "mediant" Disambiguation="integer fractions" Agda=mediant-fraction-ℤ}}
of two fractions is the quotient of the sum of the numerators by the sum of the
denominators.

## Definitions

### The mediant of two fractions

```agda
mediant-fraction-ℤ : fraction-ℤ → fraction-ℤ → fraction-ℤ
mediant-fraction-ℤ (a , b) (c , d) = (add-ℤ a c , add-positive-ℤ b d)
```

## Properties

### The mediant preserves the cross-multiplication difference

```agda
cross-mul-diff-left-mediant-fraction-ℤ :
  (x y : fraction-ℤ) →
  Id
    ( cross-mul-diff-fraction-ℤ x y)
    ( cross-mul-diff-fraction-ℤ x ( mediant-fraction-ℤ x y))
cross-mul-diff-left-mediant-fraction-ℤ (nx , dx , px) (ny , dy , py) =
  equational-reasoning
  (ny *ℤ dx -ℤ nx *ℤ dy)
  ＝ (nx *ℤ dx +ℤ ny *ℤ dx) -ℤ (nx *ℤ dx +ℤ nx *ℤ dy)
    by inv
      ( left-translation-diff-ℤ
        ( mul-ℤ ny dx)
        ( mul-ℤ nx dy)
        ( mul-ℤ nx dx))
  ＝ (nx +ℤ ny) *ℤ dx -ℤ nx *ℤ (dx +ℤ dy)
    by ap-diff-ℤ
      ( inv (right-distributive-mul-add-ℤ nx ny dx))
      ( inv (left-distributive-mul-add-ℤ nx dx dy))

cross-mul-diff-right-mediant-fraction-ℤ :
  (x y : fraction-ℤ) →
  Id
    ( cross-mul-diff-fraction-ℤ x y)
    ( cross-mul-diff-fraction-ℤ (mediant-fraction-ℤ x y) y)
cross-mul-diff-right-mediant-fraction-ℤ (nx , dx , px) (ny , dy , py) =
  equational-reasoning
  (ny *ℤ dx -ℤ nx *ℤ dy)
  ＝ (ny *ℤ dx +ℤ ny *ℤ dy) -ℤ (nx *ℤ dy +ℤ ny *ℤ dy)
    by inv
      ( right-translation-diff-ℤ
        ( mul-ℤ ny dx)
        ( mul-ℤ nx dy)
        ( mul-ℤ ny dy))
  ＝ ny *ℤ (dx +ℤ dy) -ℤ (nx +ℤ ny) *ℤ dy
    by ap-diff-ℤ
      ( inv (left-distributive-mul-add-ℤ ny dx dy))
      ( inv (right-distributive-mul-add-ℤ nx ny dy))
```

## External links

- [Mediant fraction](<https://en.wikipedia.org/wiki/Mediant_(mathematics)>) at
  Wikipedia
