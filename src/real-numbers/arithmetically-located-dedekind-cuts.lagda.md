# Arithmetically located Dedekind cuts

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.arithmetically-located-dedekind-cuts where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.archimedean-property-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups

open import logic.functoriality-existential-quantification

open import order-theory.posets

open import real-numbers.dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Definition

A pair of a [lower Dedekind cut](real-numbers.lower-dedekind-real-numbers.md)
`L` and an [upper Dedekind cut](real-numbers.upper-dedekind-real-numbers.md) `U`
is
{{#concept "arithmetically located" Disambiguation="Dedekind cut" Agda=is-arithmetically-located-lower-upper-ℝ}}
if for any [positive](elementary-number-theory.positive-rational-numbers.md)
[rational number](elementary-number-theory.rational-numbers.md) `ε : ℚ⁺`, there
exists `p, q : ℚ` where `p ∈ L` and `q ∈ U`, such that `0 < q - p < ε`.
Intuitively, when `L , U` represent the cuts of a real number `x`, `p` and `q`
are rational approximations of `x` to within `ε`.

This follows parts of Section 11 in {{#cite BauerTaylor2009}}.

## Definitions

### The predicate of being arithmetically located on pairs of lower and upper Dedekind real numbers

```agda
module _
  {l1 l2 : Level} (x : lower-ℝ l1) (y : upper-ℝ l2)
  where

  close-bounds-lower-upper-ℝ : ℚ⁺ → subtype (l1 ⊔ l2) (ℚ × ℚ)
  close-bounds-lower-upper-ℝ ε⁺ (p , q) =
    le-ℚ-Prop q (p +ℚ (rational-ℚ⁺ ε⁺)) ∧
    cut-lower-ℝ x p ∧
    cut-upper-ℝ y q

  is-arithmetically-located-prop-lower-upper-ℝ : Prop (l1 ⊔ l2)
  is-arithmetically-located-prop-lower-upper-ℝ =
    Π-Prop ℚ⁺ (λ ε⁺ → ∃ (ℚ × ℚ) (close-bounds-lower-upper-ℝ ε⁺))

  is-arithmetically-located-lower-upper-ℝ : UU (l1 ⊔ l2)
  is-arithmetically-located-lower-upper-ℝ =
    type-Prop is-arithmetically-located-prop-lower-upper-ℝ

close-bounds-ℝ : {l : Level} (x : ℝ l) → ℚ⁺ → subtype l (ℚ × ℚ)
close-bounds-ℝ x =
  close-bounds-lower-upper-ℝ (lower-real-ℝ x) (upper-real-ℝ x)
```

### The predicate of being weakly arithmetically located

```agda
module _
  {l1 l2 : Level} (x : lower-ℝ l1) (y : upper-ℝ l2)
  where

  weak-close-bounds-lower-upper-ℝ : ℚ⁺ → subtype (l1 ⊔ l2) (ℚ × ℚ)
  weak-close-bounds-lower-upper-ℝ ε⁺ (p , q) =
    leq-ℚ-Prop q (p +ℚ (rational-ℚ⁺ ε⁺)) ∧
    cut-lower-ℝ x p ∧
    cut-upper-ℝ y q

  is-weakly-arithmetically-located-prop-lower-upper-ℝ : Prop (l1 ⊔ l2)
  is-weakly-arithmetically-located-prop-lower-upper-ℝ =
    Π-Prop ℚ⁺ (λ ε⁺ → ∃ (ℚ × ℚ) (weak-close-bounds-lower-upper-ℝ ε⁺))

  is-weakly-arithmetically-located-lower-upper-ℝ : UU (l1 ⊔ l2)
  is-weakly-arithmetically-located-lower-upper-ℝ =
    type-Prop is-weakly-arithmetically-located-prop-lower-upper-ℝ
```

## Properties

### A cut is weakly arithmetically located if and only if it is arithmetically located

```agda
module _
  {l1 l2 : Level} (x : lower-ℝ l1) (y : upper-ℝ l2)
  where

  abstract
    is-arithmetically-located-is-weakly-arithmetically-located-lower-upper-ℝ :
      is-weakly-arithmetically-located-lower-upper-ℝ x y →
      is-arithmetically-located-lower-upper-ℝ x y
    is-arithmetically-located-is-weakly-arithmetically-located-lower-upper-ℝ
      W ε =
      let
        ε' = mediant-zero-ℚ⁺ ε
      in
        map-tot-exists
          ( λ (p , q) (q≤p+ε' , p<x , y<q) →
            ( concatenate-leq-le-ℚ
              ( q)
              ( p +ℚ rational-ℚ⁺ ε')
              ( p +ℚ rational-ℚ⁺ ε)
              ( q≤p+ε')
              ( preserves-le-right-add-ℚ p _ _ (le-mediant-zero-ℚ⁺ ε)) ,
              p<x ,
              y<q))
          ( W ε')

    is-weakly-arithmetically-located-is-arithmetically-located-lower-upper-ℝ :
      is-arithmetically-located-lower-upper-ℝ x y →
      is-weakly-arithmetically-located-lower-upper-ℝ x y
    is-weakly-arithmetically-located-is-arithmetically-located-lower-upper-ℝ
      H ε =
      map-tot-exists
        ( λ (p , q) (q<p+ε , p<x , y<q) → (leq-le-ℚ q<p+ε , p<x , y<q))
        ( H ε)
```

### Arithmetically located cuts are located

If a pair of lower and upper Dedekind cuts is arithmetically located, it is also
located.

```agda
module _
  {l1 l2 : Level} (x : lower-ℝ l1) (y : upper-ℝ l2)
  where

  abstract
    is-located-is-arithmetically-located-lower-upper-ℝ :
      is-arithmetically-located-lower-upper-ℝ x y →
      is-located-lower-upper-ℝ x y
    is-located-is-arithmetically-located-lower-upper-ℝ
      arithmetically-located p q p<q =
      elim-exists
        ( cut-lower-ℝ x p ∨ cut-upper-ℝ y q)
        ( λ (p' , q') (q'<p'+q-p , p'∈L , q'∈U) →
          rec-coproduct
            ( λ p<p' →
              inl-disjunction
                ( is-in-cut-le-ℚ-lower-ℝ x p p' p<p' p'∈L))
            ( λ p'≤p →
              inr-disjunction
                ( is-in-cut-le-ℚ-upper-ℝ
                  ( y)
                  ( q')
                  ( q)
                  ( concatenate-le-leq-ℚ
                    ( q')
                    ( p' +ℚ (q -ℚ p))
                    ( q)
                    ( q'<p'+q-p)
                    ( tr
                      ( leq-ℚ (p' +ℚ (q -ℚ p)))
                      ( is-identity-right-conjugation-Ab
                        ( abelian-group-add-ℚ)
                        ( p)
                        ( q))
                      ( preserves-leq-left-add-ℚ (q -ℚ p) p' p p'≤p)))
                  ( q'∈U)))
            ( decide-le-leq-ℚ p p'))
        ( arithmetically-located (positive-diff-le-ℚ p q p<q))

    is-located-is-weakly-arithmetically-located-lower-upper-ℝ :
      is-weakly-arithmetically-located-lower-upper-ℝ x y →
      is-located-lower-upper-ℝ x y
    is-located-is-weakly-arithmetically-located-lower-upper-ℝ =
      is-located-is-arithmetically-located-lower-upper-ℝ ∘
      is-arithmetically-located-is-weakly-arithmetically-located-lower-upper-ℝ
        ( x)
        ( y)
```

### The cuts of Dedekind real numbers are arithmetically located

```agda
module _
  {l : Level} (x : ℝ l)
  where

  abstract
    location-in-arithmetic-sequence-located-ℝ :
      (ε : ℚ⁺) (n : ℕ) (p : ℚ) →
      is-in-lower-cut-ℝ x p →
      is-in-upper-cut-ℝ x (p +ℚ (rational-ℤ (int-ℕ n) *ℚ rational-ℚ⁺ ε)) →
      exists
        ( ℚ)
        ( λ q → lower-cut-ℝ x q ∧ upper-cut-ℝ x (q +ℚ rational-ℚ⁺ (ε +ℚ⁺ ε)))
    location-in-arithmetic-sequence-located-ℝ ε⁺@(ε , _) zero-ℕ p p<x x<p+0ε =
      ex-falso
        ( is-disjoint-cut-ℝ
          ( x)
          ( p)
          ( p<x ,
            tr
              ( is-in-upper-cut-ℝ x)
              ( ap (p +ℚ_) (left-zero-law-mul-ℚ ε) ∙ right-unit-law-add-ℚ p)
              ( x<p+0ε)))
    location-in-arithmetic-sequence-located-ℝ
      ε⁺@(ε , _) (succ-ℕ n) p p<x x<p+nε =
      elim-disjunction
        ( ∃ ℚ (λ q → lower-cut-ℝ x q ∧ upper-cut-ℝ x (q +ℚ (ε +ℚ ε))))
        ( λ p+ε<x →
          location-in-arithmetic-sequence-located-ℝ
            ( ε⁺)
            ( n)
            ( p +ℚ ε)
            ( p+ε<x)
            ( tr
              ( is-in-upper-cut-ℝ x)
              ( equational-reasoning
                p +ℚ (rational-ℤ (int-ℕ (succ-ℕ n)) *ℚ ε)
                ＝ p +ℚ (succ-ℚ (rational-ℤ (int-ℕ n)) *ℚ ε)
                  by ap (p +ℚ_) (ap (_*ℚ ε) (inv (succ-rational-int-ℕ n)))
                ＝ p +ℚ (ε +ℚ (rational-ℤ (int-ℕ n) *ℚ ε))
                  by ap (p +ℚ_) (mul-left-succ-ℚ _ _)
                ＝ (p +ℚ ε) +ℚ rational-ℤ (int-ℕ n) *ℚ ε
                  by inv (associative-add-ℚ _ _ _))
              ( x<p+nε)))
        ( λ x<p+2ε →
          intro-exists
            ( p)
            ( p<x ,
              tr
                ( is-in-upper-cut-ℝ x)
                ( associative-add-ℚ p ε ε)
                ( x<p+2ε)))
        ( is-located-lower-upper-cut-ℝ
          ( x)
          ( p +ℚ ε)
          ( (p +ℚ ε) +ℚ ε)
          ( le-right-add-rational-ℚ⁺ (p +ℚ ε) ε⁺))

    is-arithmetically-located-ℝ :
      is-arithmetically-located-lower-upper-ℝ (lower-real-ℝ x) (upper-real-ℝ x)
    is-arithmetically-located-ℝ ε⁺@(ε , _) =
      let
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℚ × ℚ)
              ( close-bounds-lower-upper-ℝ
                ( lower-real-ℝ x)
                ( upper-real-ℝ x)
                ( ε⁺)))
      in do
        ε'⁺@(ε' , pos-ε') , 2ε'<ε ← double-le-ℚ⁺ ε⁺
        p , p<x ← is-inhabited-lower-cut-ℝ x
        q , x<q ← is-inhabited-upper-cut-ℝ x
        n , q-p<nε' ← archimedean-property-ℚ ε' (q -ℚ p) pos-ε'
        let nℚ = rational-ℤ (int-ℕ n)
        r , r<x , x<r+2ε' ←
          location-in-arithmetic-sequence-located-ℝ
            ( ε'⁺)
            ( n)
            ( p)
            ( p<x)
            ( le-upper-cut-ℝ
              ( x)
              ( q)
              ( p +ℚ (nℚ *ℚ ε'))
              ( tr
                ( le-ℚ q)
                ( commutative-add-ℚ (nℚ *ℚ ε') p)
                ( le-transpose-left-diff-ℚ q p (nℚ *ℚ ε') ( q-p<nε')))
              ( x<q))
        intro-exists
          ( r , r +ℚ (ε' +ℚ ε'))
          ( preserves-le-right-add-ℚ r (ε' +ℚ ε') ε 2ε'<ε ,
            r<x ,
            x<r+2ε')
```

### For any real number `x` and any `ε : ℚ⁺`, there exists `n : ℕ` such that if `q < x < q + ε`, then `|q| < n` and `|q +ℚ ε| < n`

```agda
abstract
  natural-bound-location-ℝ :
    {l : Level} → (x : ℝ l) (ε : ℚ⁺) →
    exists
      ( ℕ)
      ( λ n →
        Π-Prop
          ( type-subtype (close-bounds-ℝ x ε))
          ( λ ((q , q') , _) →
            le-ℚ-Prop
              ( max-ℚ (rational-abs-ℚ q) (rational-abs-ℚ q'))
              ( rational-ℕ n)))
  natural-bound-location-ℝ x ε⁺@(ε , _) =
    let
      open
        do-syntax-trunc-Prop
          ( ∃
            ( ℕ)
            ( λ n →
              Π-Prop
                ( type-subtype (close-bounds-ℝ x ε⁺))
                ( λ ((q , q') , _) →
                  le-ℚ-Prop
                    ( max-ℚ (rational-abs-ℚ q) (rational-abs-ℚ q'))
                    ( rational-ℕ n))))
      open inequality-reasoning-Poset ℚ-Poset
    in do
      (p , p<x) ← is-inhabited-lower-cut-ℝ x
      (q , x<q) ← is-inhabited-upper-cut-ℝ x
      (n , max|p||q|<n) ←
        exists-greater-natural-ℚ (max-ℚ (rational-abs-ℚ p) (rational-abs-ℚ q))
      (m , ε<m) ← exists-greater-natural-ℚ ε
      intro-exists
        ( m +ℕ n +ℕ m)
        ( λ ((a , b) , b<a+ε , a<x , x<b) →
          let
            |a|≤m+n =
              leq-abs-leq-leq-neg-ℚ
                ( a)
                ( rational-ℕ (m +ℕ n))
                ( chain-of-inequalities
                    a
                    ≤ q
                      by leq-lower-upper-cut-ℝ x a q a<x x<q
                    ≤ rational-abs-ℚ q
                      by leq-abs-ℚ q
                    ≤ ε +ℚ rational-abs-ℚ q
                      by leq-left-add-rational-ℚ⁺ _ ε⁺
                    ≤ rational-ℕ m +ℚ
                      max-ℚ (rational-abs-ℚ p) (rational-abs-ℚ q)
                      by
                        preserves-leq-add-ℚ
                          ( leq-le-ℚ ε<m)
                          ( leq-right-max-ℚ _ _)
                    ≤ rational-ℕ m +ℚ rational-ℕ n
                      by preserves-leq-right-add-ℚ _ _ _ (leq-le-ℚ max|p||q|<n)
                    ≤ rational-ℕ (m +ℕ n)
                      by leq-eq-ℚ _ _ (add-rational-ℕ _ _))
                ( chain-of-inequalities
                    neg-ℚ a
                    ≤ neg-ℚ (b -ℚ ε)
                      by
                        neg-leq-ℚ
                          ( leq-transpose-right-add-ℚ _ _ _ (leq-le-ℚ b<a+ε))
                    ≤ ε -ℚ b
                      by leq-eq-ℚ _ _ (distributive-neg-diff-ℚ _ _)
                    ≤ ε -ℚ p
                      by
                        preserves-leq-right-add-ℚ ε
                          ( neg-ℚ b)
                          ( neg-ℚ p)
                          ( neg-leq-ℚ
                            ( leq-lower-upper-cut-ℝ x p b p<x x<b))
                    ≤ rational-abs-ℚ (ε -ℚ p)
                      by leq-abs-ℚ _
                    ≤ rational-abs-ℚ ε +ℚ rational-abs-ℚ p
                      by triangle-inequality-abs-diff-ℚ ε p
                    ≤ ε +ℚ max-ℚ (rational-abs-ℚ p) (rational-abs-ℚ q)
                      by
                        preserves-leq-add-ℚ
                          ( leq-eq-ℚ _ _ (rational-abs-rational-ℚ⁺ ε⁺))
                          ( leq-left-max-ℚ _ _)
                    ≤ rational-ℕ m +ℚ rational-ℕ n
                      by
                        preserves-leq-add-ℚ
                          ( leq-le-ℚ ε<m)
                          ( leq-le-ℚ max|p||q|<n)
                    ≤ rational-ℕ (m +ℕ n)
                      by leq-eq-ℚ _ _ (add-rational-ℕ _ _))
            |b|≤|a|+ε =
              leq-abs-leq-leq-neg-ℚ b (rational-abs-ℚ a +ℚ ε)
                ( chain-of-inequalities
                    b
                    ≤ a +ℚ ε
                      by leq-le-ℚ b<a+ε
                    ≤ rational-abs-ℚ (a +ℚ ε)
                      by leq-abs-ℚ _
                    ≤ rational-abs-ℚ a +ℚ rational-abs-ℚ ε
                      by triangle-inequality-abs-ℚ _ _
                    ≤ rational-abs-ℚ a +ℚ ε
                      by
                        leq-eq-ℚ _ _
                          ( ap-add-ℚ refl (rational-abs-rational-ℚ⁺ ε⁺)))
                ( chain-of-inequalities
                    neg-ℚ b
                    ≤ neg-ℚ a
                      by neg-leq-ℚ (leq-lower-upper-cut-ℝ x a b a<x x<b)
                    ≤ rational-abs-ℚ a
                      by neg-leq-abs-ℚ a
                    ≤ rational-abs-ℚ a +ℚ ε
                      by leq-right-add-rational-ℚ⁺ _ ε⁺)
          in
            concatenate-leq-le-ℚ
              ( max-ℚ (rational-abs-ℚ a) (rational-abs-ℚ b))
              ( rational-ℕ (m +ℕ n) +ℚ ε)
              ( rational-ℕ (m +ℕ n +ℕ m))
              ( leq-max-leq-both-ℚ _ _ _
                ( transitive-leq-ℚ _ (rational-ℕ (m +ℕ n)) _
                  ( leq-right-add-rational-ℚ⁺ _ ε⁺)
                  ( |a|≤m+n))
                ( transitive-leq-ℚ _ (rational-abs-ℚ a +ℚ ε) _
                  ( preserves-leq-left-add-ℚ _ _ _ |a|≤m+n)
                  ( |b|≤|a|+ε)))
              ( tr
                ( le-ℚ (rational-ℕ (m +ℕ n) +ℚ ε))
                ( add-rational-ℕ _ _)
                ( preserves-le-right-add-ℚ _ _ _ ε<m)))
```

## References

{{#bibliography}}
