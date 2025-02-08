# Arithmetically located Dedekind cuts

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.arithmetically-located-dedekind-cuts where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.archimedean-property-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups

open import real-numbers.dedekind-real-numbers
```

</details>

## Definition

A [Dedekind cut](real-numbers.dedekind-real-numbers.md) `(L, U)` is
{{#concept "arithmetically located" Disambiguation="Dedekind cut"}} if for any
positive [rational number](elementary-number-theory.rational-numbers.md)
`ε : ℚ`, there exist `p, q : ℚ` such that `0 < q - p < ε`, `p ∈ L`, and `q ∈ U`.
Intuitively, when `L , U` represent the Dedekind cuts of a real number `x`, `p`
and `q` are rational approximations of `x` to within `ε`. This follows parts of
Section 11 in {{#cite BauerTaylor2009}}.

## Definitions

### The predicate of being arithmetically located on pairs of subtypes of rational numbers

```agda
module _
  {l : Level} (L : subtype l ℚ) (U : subtype l ℚ)
  where

  is-arithmetically-located-pair-of-subtypes-ℚ : UU l
  is-arithmetically-located-pair-of-subtypes-ℚ =
    (ε : ℚ⁺) →
    exists
      ( ℚ × ℚ)
      ( λ (p , q) → le-ℚ-Prop q (p +ℚ rational-ℚ⁺ ε) ∧ L p ∧ U q)
```

## Properties

### Arithmetically located cuts are located

If a cut is arithmetically located and closed under strict inequality on the
rational numbers, it is also located.

```agda
module _
  {l : Level} (L : subtype l ℚ) (U : subtype l ℚ)
  where

  abstract
    is-located-is-arithmetically-located-pair-of-subtypes-ℚ :
      is-arithmetically-located-pair-of-subtypes-ℚ L U →
      ((p q : ℚ) → le-ℚ p q → is-in-subtype L q → is-in-subtype L p) →
      ((p q : ℚ) → le-ℚ p q → is-in-subtype U p → is-in-subtype U q) →
      (p q : ℚ) → le-ℚ p q → type-disjunction-Prop (L p) (U q)
    is-located-is-arithmetically-located-pair-of-subtypes-ℚ
      arithmetically-located lower-closed upper-closed p q p<q =
      elim-exists
        ( L p ∨ U q)
        ( λ (p' , q') (q'<p'+ε , p'-in-l , q'-in-u) →
          rec-coproduct
            ( λ p<p' → inl-disjunction (lower-closed p p' p<p' p'-in-l))
            ( λ p'≤p →
              inr-disjunction
                ( upper-closed
                  ( q')
                  ( q)
                  ( concatenate-le-leq-ℚ
                    ( q')
                    ( p' +ℚ (q -ℚ p))
                    ( q)
                    ( q'<p'+ε)
                    ( tr
                      ( leq-ℚ (p' +ℚ q -ℚ p))
                      ( equational-reasoning
                        p +ℚ (q -ℚ p)
                        ＝ (p +ℚ q) -ℚ p
                          by inv (associative-add-ℚ p q (neg-ℚ p))
                        ＝ q
                          by is-identity-conjugation-Ab abelian-group-add-ℚ p q)
                      ( backward-implication
                        ( iff-translate-right-leq-ℚ (q -ℚ p) p' p)
                        ( p'≤p))))
                  ( q'-in-u)))
            ( decide-le-leq-ℚ p p'))
        ( arithmetically-located (positive-diff-le-ℚ p q p<q))
```

### Real numbers are arithmetically located

```agda
module _
  {l : Level}
  (x : ℝ l)
  where

  abstract
    arithmetic-location-in-arithmetic-sequence :
      (p ε : ℚ) →
      (n : ℕ) →
      is-positive-ℚ ε →
      is-in-lower-cut-ℝ x p →
      is-in-upper-cut-ℝ x (p +ℚ (rational-ℤ (int-ℕ n) *ℚ ε)) →
      exists ℚ ( λ q → lower-cut-ℝ x q ∧ upper-cut-ℝ x (q +ℚ ε +ℚ ε))
    arithmetic-location-in-arithmetic-sequence
      p ε zero-ℕ positive-ε p-in-L p-plus-0-ε-in-U =
      ex-falso
        ( is-disjoint-cut-ℝ
          ( x)
          ( p)
          ( p-in-L ,
            tr
              ( is-in-upper-cut-ℝ x)
              ( ap (p +ℚ_) (left-zero-law-mul-ℚ ε) ∙ right-unit-law-add-ℚ p)
              ( p-plus-0-ε-in-U)))
    arithmetic-location-in-arithmetic-sequence
      p ε (succ-ℕ n) positive-ε p-in-L p-plus-sn-ε-in-U =
      elim-disjunction
        ( ∃ ℚ ( λ q → lower-cut-ℝ x q ∧ upper-cut-ℝ x (q +ℚ ε +ℚ ε)))
        ( λ p+ε-in-L →
          arithmetic-location-in-arithmetic-sequence
            ( p +ℚ ε)
            ( ε)
            ( n)
            ( positive-ε)
            ( p+ε-in-L)
            ( tr
              ( is-in-upper-cut-ℝ x)
              ( equational-reasoning
                p +ℚ (rational-ℤ (int-ℕ (succ-ℕ n)) *ℚ ε)
                ＝ p +ℚ (rational-ℤ (succ-ℤ (int-ℕ n)) *ℚ ε)
                  by ap
                      ( λ x → p +ℚ (rational-ℤ x *ℚ ε))
                      ( inv (succ-int-ℕ n))
                ＝ p +ℚ (succ-ℚ (rational-ℤ (int-ℕ n)) *ℚ ε)
                  by ap (p +ℚ_) (ap (_*ℚ ε) (inv (succ-rational-ℤ (int-ℕ n))))
                ＝ p +ℚ (ε +ℚ rational-ℤ (int-ℕ n) *ℚ ε)
                  by ap (p +ℚ_) (mul-left-succ-ℚ (rational-ℤ (int-ℕ n)) ε)
                ＝ (p +ℚ ε) +ℚ (rational-ℤ (int-ℕ n) *ℚ ε)
                  by inv (associative-add-ℚ p ε (rational-ℤ (int-ℕ n) *ℚ ε)))
              ( p-plus-sn-ε-in-U)))
        ( λ p+2ε-in-U → intro-exists p (p-in-L , p+2ε-in-U))
        ( is-located-lower-upper-cut-ℝ
          ( x)
          ( p +ℚ ε)
          ( (p +ℚ ε) +ℚ ε)
          ( le-right-add-rational-ℚ⁺ (p +ℚ ε) (ε , positive-ε)))

  abstract
    bounded-arithmetic-location-twice-ε :
      (p q ε : ℚ) →
      is-positive-ℚ ε →
      is-in-lower-cut-ℝ x p →
      is-in-upper-cut-ℝ x q →
      exists
        ℚ
        ( λ r →
          lower-cut-ℝ x r ∧
          upper-cut-ℝ x (r +ℚ ε +ℚ ε))
    bounded-arithmetic-location-twice-ε p q ε pos-ε p-in-L q-in-U =
      elim-exists
        ( ∃ ℚ ( λ r → lower-cut-ℝ x r ∧ upper-cut-ℝ x (r +ℚ ε +ℚ ε)))
        ( λ n q-p<nε →
          arithmetic-location-in-arithmetic-sequence
            ( p)
            ( ε)
            ( n)
            ( pos-ε)
            ( p-in-L)
            ( le-upper-cut-ℝ
              ( x)
              ( q)
              ( p +ℚ rational-ℤ (int-ℕ n) *ℚ ε)
              ( tr
                ( λ r → le-ℚ r (p +ℚ rational-ℤ (int-ℕ n) *ℚ ε))
                ( is-identity-right-conjugation-Ab abelian-group-add-ℚ p q)
                ( preserves-le-right-add-ℚ
                  ( p)
                  ( q -ℚ p)
                  ( rational-ℤ (int-ℕ n) *ℚ ε) q-p<nε))
              ( q-in-U)))
        ( archimedean-property-ℚ ε (q -ℚ p) pos-ε)

  abstract
    arithmetically-located-ℝ :
      is-arithmetically-located-pair-of-subtypes-ℚ
        ( lower-cut-ℝ x)
        ( upper-cut-ℝ x)
    arithmetically-located-ℝ ε⁺@(ε , positive-ε) =
      elim-exists
        ( claim)
        ( λ p p-in-L →
          elim-exists
            ( claim)
            ( λ q q-in-U →
              elim-exists
                ( claim)
                ( λ (ε' , pos-ε') 2ε'<ε →
                  elim-exists
                    ( claim)
                    ( λ r (r-in-L , r+2ε'-in-U) →
                      intro-exists
                        ( r , r +ℚ ε' +ℚ ε')
                        ( tr
                            ( λ s → le-ℚ s (r +ℚ ε))
                            ( inv (associative-add-ℚ r ε' ε'))
                            ( preserves-le-right-add-ℚ r (ε' +ℚ ε') ε 2ε'<ε) ,
                          r-in-L ,
                          r+2ε'-in-U))
                    ( bounded-arithmetic-location-twice-ε
                      ( p)
                      ( q)
                      ( ε')
                      ( pos-ε')
                      ( p-in-L)
                      ( q-in-U)))
                ( double-le-ℚ⁺ ε⁺))
            ( is-inhabited-upper-cut-ℝ x))
        ( is-inhabited-lower-cut-ℝ x)
      where
        claim : Prop l
        claim =
          ∃ ( ℚ × ℚ)
            ( λ (p , q) →
              le-ℚ-Prop q (p +ℚ ε) ∧
              lower-cut-ℝ x p ∧
              upper-cut-ℝ x q)
```

## References

{{#bibliography}}
