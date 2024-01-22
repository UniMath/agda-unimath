# Dedekind real numbers

```agda
module real-numbers.dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.truncated-types
open import foundation.universe-levels

open import foundation-core.truncation-levels
```

</details>

## Idea

A
{{#concept "Dedekind cut" Agda=is-dedekind-cut WD="Dedekind cut" WDID=Q851333}}
consists of a [pair](foundation.dependent-pair-types.md) `(L , U)` of
[subtypes](foundation-core.subtypes.md) of
[the rational numbers](elementary-number-theory.rational-numbers.md) `ℚ`,
satisfying the following four conditions

1. _Inhabitedness_. Both `L` and `U` are
   [inhabited](foundation.inhabited-subtypes.md) subtypes of `ℚ`.
2. _Roundedness_. A rational number `q` is in `L`
   [if and only if](foundation.logical-equivalences.md) there
   [exists](foundation.existential-quantification.md) `q < r` such that `r ∈ L`,
   and a rational number `r` is in `U` if and only if there exists `q < r` such
   that `q ∈ U`.
3. _Disjointness_. `L` and `U` are disjoint subsets of `ℚ`.
4. _Locatedness_. If `q < r` then `q ∈ L` or `r ∈ U`.

The type of {{#concept "Dedekind real numbers" Agda=ℝ}} is the type of all
Dedekind cuts. The Dedekind real numbers will be taken as the standard
definition of the real numbers in the `agda-unimath` library.

## Definition

### Dedekind cuts

```agda
module _
  {l1 l2 : Level} (L : subtype l1 ℚ) (U : subtype l2 ℚ)
  where

  is-dedekind-cut-Prop : Prop (l1 ⊔ l2)
  is-dedekind-cut-Prop =
    prod-Prop
      ( prod-Prop (exists-Prop ℚ L) (exists-Prop ℚ U))
      ( prod-Prop
        ( prod-Prop
          ( Π-Prop ℚ
            ( λ q →
              iff-Prop
                ( L q)
                ( exists-Prop ℚ (λ r → prod-Prop (le-ℚ-Prop q r) (L r)))))
          ( Π-Prop ℚ
            ( λ r →
              iff-Prop
                ( U r)
                ( exists-Prop ℚ (λ q → prod-Prop (le-ℚ-Prop q r) (U q))))))
        ( prod-Prop
          ( Π-Prop ℚ (λ q → neg-Prop (prod-Prop (L q) (U q))))
          ( Π-Prop ℚ
            ( λ q →
              Π-Prop ℚ
                ( λ r →
                  hom-Prop
                    ( le-ℚ-Prop q r)
                    ( disjunction-Prop (L q) (U r)))))))

  is-dedekind-cut : UU (l1 ⊔ l2)
  is-dedekind-cut = type-Prop is-dedekind-cut-Prop

  is-prop-is-dedekind-cut : is-prop is-dedekind-cut
  is-prop-is-dedekind-cut = is-prop-type-Prop is-dedekind-cut-Prop
```

### The Dedekind real numbers

```agda
ℝ : (l : Level) → UU (lsuc l)
ℝ l = Σ (subtype l ℚ) (λ L → Σ (subtype l ℚ) (is-dedekind-cut L))
```

## Properties

### The Dedekind real numbers form a set

```agda
abstract
  is-set-ℝ : (l : Level) → is-set (ℝ l)
  is-set-ℝ l =
    is-set-Σ
      ( is-set-function-type (is-trunc-Truncated-Type neg-one-𝕋))
      ( λ x →
        ( is-set-Σ
          ( is-set-function-type (is-trunc-Truncated-Type neg-one-𝕋))
          ( λ y →
            ( is-set-is-prop
              ( is-prop-type-Prop
                ( is-dedekind-cut-Prop x y))))))

ℝ-Set : (l : Level) → Set (lsuc l)
pr1 (ℝ-Set l) = ℝ l
pr2 (ℝ-Set l) = is-set-ℝ l
```

## References

1. Section 11.2 of Univalent Foundations Project, _Homotopy Type Theory –
   Univalent Foundations of Mathematics_ (2013)
   ([website](https://homotopytypetheory.org/book/),
   [arXiv:1308.0729](https://arxiv.org/abs/1308.0729))

## External links

- [DedekindReals.Type](https://www.cs.bham.ac.uk/~mhe/TypeTopology/DedekindReals.Type.html)
  at TypeTopology
- [Dedekind cut](https://ncatlab.org/nlab/show/Dedekind+cut) at $n$Lab
- [Dedekind cut](https://en.wikipedia.org/wiki/Dedekind_cut) at Wikipedia
- [Construction of the real numbers by Dedekind cuts](https://en.wikipedia.org/wiki/Construction_of_the_real_numbers#Construction_by_Dedekind_cuts)
  at Wikipedia
- [Dedekind cut](https://www.britannica.com/science/Dedekind-cut) at Britannica
