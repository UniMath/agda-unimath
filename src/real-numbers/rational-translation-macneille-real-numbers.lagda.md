# Rational translation of MacNeille real numbers

```agda
module real-numbers.rational-translation-macneille-real-numbers where
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
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-located-macneille-real-numbers
open import real-numbers.addition-lower-dedekind-real-numbers
open import real-numbers.inequalities-translation-macneille-real-numbers
open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.located-macneille-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.raising-universe-levels-located-macneille-real-numbers
open import real-numbers.raising-universe-levels-macneille-real-numbers
open import real-numbers.raising-universe-levels-rational-macneille-real-numbers
open import real-numbers.rational-macneille-real-numbers
open import real-numbers.similarity-macneille-real-numbers
open import real-numbers.strict-inequality-macneille-real-numbers
open import real-numbers.translation-macneille-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Definitions

```agda
translate-ℚ-macneille-ℝ :
  {l : Level} → ℚ → macneille-ℝ l → macneille-ℝ l
translate-ℚ-macneille-ℝ q =
  translate-macneille-ℝ (located-macneille-real-ℚ q)

translate-ℚ⁺-macneille-ℝ :
  {l : Level} → ℚ⁺ → macneille-ℝ l → macneille-ℝ l
translate-ℚ⁺-macneille-ℝ q⁺ =
  translate-ℚ-macneille-ℝ (rational-ℚ⁺ q⁺)
```

## Properties

### Translation laws

```agda
abstract opaque
  unfolding translate-macneille-ℝ

  translate-add-ℚ-macneille-ℝ :
    {l : Level} (p q : ℚ) (x : macneille-ℝ l) →
    translate-ℚ-macneille-ℝ p (translate-ℚ-macneille-ℝ q x) ＝
    translate-ℚ-macneille-ℝ (p +ℚ q) x
  translate-add-ℚ-macneille-ℝ p q x =
    eq-eq-lower-real-macneille-ℝ
      ( translate-ℚ-macneille-ℝ p (translate-ℚ-macneille-ℝ q x))
      ( translate-ℚ-macneille-ℝ (p +ℚ q) x)
      ( ( inv
          ( associative-add-lower-ℝ
            ( lower-real-macneille-ℝ (macneille-real-ℚ p))
            ( lower-real-macneille-ℝ (macneille-real-ℚ q))
            ( lower-real-macneille-ℝ x))) ∙
        ( ap
          ( λ y → add-lower-ℝ y (lower-real-macneille-ℝ x))
          ( ap lower-real-macneille-ℝ (add-macneille-real-ℚ p q))))

  add-raise-macneille-real-ℚ :
    {l : Level} (p q : ℚ) →
    translate-macneille-ℝ
      ( located-raise-macneille-ℝ l (located-macneille-real-ℚ p))
      ( raise-macneille-ℝ l (macneille-real-ℚ q)) ＝
    raise-macneille-ℝ l (macneille-real-ℚ (p +ℚ q))
  add-raise-macneille-real-ℚ {l} p q =
    translate-raise-macneille-ℝ ∙
    ap (raise-macneille-ℝ l) (add-macneille-real-ℚ p q)

  eq-add-translate-raise-macneille-real-ℚ :
    {l : Level} (q r : ℚ) →
    translate-ℚ-macneille-ℝ q (raise-macneille-ℝ l (macneille-real-ℚ r)) ＝
    raise-macneille-ℝ l (macneille-real-ℚ (q +ℚ r))
  eq-add-translate-raise-macneille-real-ℚ {l} q r =
    eq-sim-macneille-ℝ
      ( transitive-sim-macneille-ℝ _ _ _
        ( sim-eq-macneille-ℝ (add-raise-macneille-real-ℚ {l} q r))
        ( preserves-sim-translate-macneille-ℝ
          { x = located-macneille-real-ℚ q}
          { x' = located-raise-macneille-ℝ l (located-macneille-real-ℚ q)}
          { y = raise-macneille-ℝ l (macneille-real-ℚ r)}
          { y' = raise-macneille-ℝ l (macneille-real-ℚ r)}
          ( sim-raise-macneille-ℝ l (macneille-real-ℚ q))
          ( refl-sim-macneille-ℝ (raise-macneille-ℝ l (macneille-real-ℚ r)))))

  eq-add-translate-raise-macneille-real-ℚ' :
    {l : Level} (q r : ℚ) →
    translate-ℚ-macneille-ℝ q (raise-macneille-real-ℚ l r) ＝
    raise-macneille-real-ℚ l (q +ℚ r)
  eq-add-translate-raise-macneille-real-ℚ' {l} q r =
    ( ap
      ( translate-ℚ-macneille-ℝ q)
      ( eq-raise-macneille-real-ℚ-raise-macneille-ℝ r)) ∙
    ( eq-add-translate-raise-macneille-real-ℚ {l} q r) ∙
    ( inv (eq-raise-macneille-real-ℚ-raise-macneille-ℝ (q +ℚ r)))

  preserves-leq-translate-raise-ℚ-macneille-ℝ :
    {l : Level} (x : macneille-ℝ l) (p q : ℚ) →
    leq-ℚ p q →
    leq-macneille-ℝ
      ( translate-macneille-ℝ (raise-located-macneille-real-ℚ l p) x)
      ( translate-macneille-ℝ (raise-located-macneille-real-ℚ l q) x)
  preserves-leq-translate-raise-ℚ-macneille-ℝ {l} x p q p≤q =
    preserves-leq-left-translate-macneille-ℝ
      ( raise-located-macneille-real-ℚ l p)
      ( raise-located-macneille-real-ℚ l q)
      ( x)
      ( leq-raise-macneille-real-ℚ p q p≤q)
```

```agda
abstract
  is-retraction-translate-neg-ℚ-macneille-ℝ :
    {l : Level} (q : ℚ) (x : macneille-ℝ l) →
    translate-ℚ-macneille-ℝ (neg-ℚ q) (translate-ℚ-macneille-ℝ q x) ＝ x
  is-retraction-translate-neg-ℚ-macneille-ℝ q x =
    ( translate-add-ℚ-macneille-ℝ (neg-ℚ q) q x) ∙
    ( ap
      ( λ z → translate-macneille-ℝ z x)
      ( ap located-macneille-real-ℚ (left-inverse-law-add-ℚ q))) ∙
    ( left-unit-law-translate-macneille-ℝ x)

  is-section-translate-neg-ℚ-macneille-ℝ :
    {l : Level} (q : ℚ) (x : macneille-ℝ l) →
    translate-ℚ-macneille-ℝ q (translate-ℚ-macneille-ℝ (neg-ℚ q) x) ＝ x
  is-section-translate-neg-ℚ-macneille-ℝ q x =
    ( translate-add-ℚ-macneille-ℝ q (neg-ℚ q) x) ∙
    ( ap
      ( λ z → translate-macneille-ℝ z x)
      ( ap located-macneille-real-ℚ (right-inverse-law-add-ℚ q))) ∙
    ( left-unit-law-translate-macneille-ℝ x)
```

### Reflection of order

```agda
preserves-leq-offset-translate-ℚ-macneille-ℝ :
  {l1 l2 : Level} (q : ℚ) (x : macneille-ℝ l1) (y : macneille-ℝ l2) →
  leq-macneille-ℝ x y →
  leq-macneille-ℝ
    ( translate-ℚ-macneille-ℝ q x)
    ( translate-ℚ-macneille-ℝ q y)
preserves-leq-offset-translate-ℚ-macneille-ℝ q =
  preserves-leq-right-translate-macneille-ℝ (located-macneille-real-ℚ q)

abstract
  reflects-leq-offset-translate-ℚ-macneille-ℝ :
    {l : Level} (q : ℚ) (x y : macneille-ℝ l) →
    leq-macneille-ℝ
      ( translate-ℚ-macneille-ℝ q x)
      ( translate-ℚ-macneille-ℝ q y) →
    leq-macneille-ℝ x y
  reflects-leq-offset-translate-ℚ-macneille-ℝ q x y q+x≤q+y =
    binary-tr
      leq-macneille-ℝ
      ( is-retraction-translate-neg-ℚ-macneille-ℝ q x)
      ( is-retraction-translate-neg-ℚ-macneille-ℝ q y)
      ( preserves-leq-offset-translate-ℚ-macneille-ℝ
        ( neg-ℚ q)
        ( translate-ℚ-macneille-ℝ q x)
        ( translate-ℚ-macneille-ℝ q y)
        ( q+x≤q+y))

  leq-transpose-neg-translate-ℚ-macneille-ℝ :
    {l : Level} (q : ℚ) (x y : macneille-ℝ l) →
    leq-macneille-ℝ (translate-ℚ-macneille-ℝ q x) y →
    leq-macneille-ℝ x (translate-ℚ-macneille-ℝ (neg-ℚ q) y)
  leq-transpose-neg-translate-ℚ-macneille-ℝ q x y q+x≤y =
    reflects-leq-offset-translate-ℚ-macneille-ℝ q x
      ( translate-ℚ-macneille-ℝ (neg-ℚ q) y)
      ( tr
        ( leq-macneille-ℝ (translate-ℚ-macneille-ℝ q x))
        ( inv (is-section-translate-neg-ℚ-macneille-ℝ q y))
        ( q+x≤y))

iff-translate-ℚ-macneille-ℝ :
  {l : Level} (q : ℚ) (x y : macneille-ℝ l) →
  leq-macneille-ℝ x y ↔
  leq-macneille-ℝ
    ( translate-ℚ-macneille-ℝ q x)
    ( translate-ℚ-macneille-ℝ q y)
iff-translate-ℚ-macneille-ℝ q x y =
  ( preserves-leq-offset-translate-ℚ-macneille-ℝ q x y ,
    reflects-leq-offset-translate-ℚ-macneille-ℝ q x y)
```

### If `q : ℚ⁺` then `q + x ≰ x`

```agda
module _
  {l : Level} (q⁺ : ℚ⁺) (x : macneille-ℝ l)
  (let q = rational-ℚ⁺ q⁺)
  where

  abstract
    leq-self-translate-multiple-ℚ⁺-macneille-ℝ :
      leq-macneille-ℝ (translate-ℚ⁺-macneille-ℝ q⁺ x) x →
      (n : ℕ) →
      leq-macneille-ℝ (translate-ℚ-macneille-ℝ (rational-ℕ n *ℚ q) x) x
    leq-self-translate-multiple-ℚ⁺-macneille-ℝ q+x≤x zero-ℕ =
      tr
        ( λ y → leq-macneille-ℝ y x)
        ( ( inv (left-unit-law-translate-macneille-ℝ x)) ∙
          ( inv
            ( ap
              ( λ r → translate-ℚ-macneille-ℝ r x)
              ( left-zero-law-mul-ℚ q))))
        ( refl-leq-macneille-ℝ x)
    leq-self-translate-multiple-ℚ⁺-macneille-ℝ q+x≤x (succ-ℕ n) =
      tr
        ( λ y → leq-macneille-ℝ y x)
        ( ( translate-add-ℚ-macneille-ℝ q (rational-ℕ n *ℚ q) x) ∙
          ( ap
            ( λ r → translate-ℚ-macneille-ℝ r x)
            ( eq-succ-mul-rational-ℕ-right-ℚ n q)))
        ( transitive-leq-macneille-ℝ
          ( translate-ℚ⁺-macneille-ℝ q⁺
            ( translate-ℚ-macneille-ℝ (rational-ℕ n *ℚ q) x))
          ( translate-ℚ⁺-macneille-ℝ q⁺ x)
          ( x)
          ( q+x≤x)
          ( preserves-leq-offset-translate-ℚ-macneille-ℝ
            ( q)
            ( translate-ℚ-macneille-ℝ (rational-ℕ n *ℚ q) x)
            ( x)
            ( leq-self-translate-multiple-ℚ⁺-macneille-ℝ q+x≤x n)))

    not-leq-self-translate-ℚ⁺-macneille-ℝ :
      ¬ leq-macneille-ℝ (translate-ℚ⁺-macneille-ℝ q⁺ x) x
    not-leq-self-translate-ℚ⁺-macneille-ℝ q+x≤x =
      apply-twice-universal-property-trunc-Prop
        ( exists-lesser-rational-macneille-ℝ x)
        ( exists-greater-rational-macneille-ℝ x)
        ( empty-Prop)
        ( λ (p , p<x) (r , x<r) →
          let
            (n , r-p<n⋅q) =
              bound-archimedean-property-ℚ q
                ( r -ℚ p)
                ( is-positive-rational-ℚ⁺ q⁺)

            r≤p+n⋅q =
              tr
                ( λ t → leq-ℚ t (p +ℚ (rational-ℕ n *ℚ q)))
                ( is-identity-right-conjugation-add-ℚ p r)
                ( preserves-leq-right-add-ℚ
                  ( p)
                  ( r -ℚ p)
                  ( rational-ℕ n *ℚ q)
                  ( leq-le-ℚ r-p<n⋅q))

            p+n⋅q≤x =
              tr
                ( λ y → leq-macneille-ℝ y x)
                ( add-macneille-real-ℚ (rational-ℕ n *ℚ q) p ∙
                  ( ap
                    ( macneille-real-ℚ)
                    ( commutative-add-ℚ (rational-ℕ n *ℚ q) p)))
                ( transitive-leq-macneille-ℝ
                  ( translate-ℚ-macneille-ℝ
                    ( rational-ℕ n *ℚ q)
                    ( macneille-real-ℚ p))
                  ( translate-ℚ-macneille-ℝ (rational-ℕ n *ℚ q) x)
                  ( x)
                  ( leq-self-translate-multiple-ℚ⁺-macneille-ℝ q+x≤x n)
                  ( preserves-leq-offset-translate-ℚ-macneille-ℝ
                    ( rational-ℕ n *ℚ q)
                    ( macneille-real-ℚ p)
                    ( x)
                    ( leq-le-macneille-ℝ p<x)))

            p+n⋅q<r : le-ℚ (p +ℚ (rational-ℕ n *ℚ q)) r
            p+n⋅q<r =
              reflects-le-macneille-real-ℚ
                ( concatenate-leq-le-macneille-ℝ
                  ( macneille-real-ℚ (p +ℚ (rational-ℕ n *ℚ q)))
                  ( x)
                  ( macneille-real-ℚ r)
                  ( p+n⋅q≤x)
                  ( x<r))
          in
          not-leq-le-ℚ (p +ℚ (rational-ℕ n *ℚ q)) r p+n⋅q<r r≤p+n⋅q)
```
