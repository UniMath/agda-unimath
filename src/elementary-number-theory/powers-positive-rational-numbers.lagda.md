# Powers of positive rational numbers

```agda
module elementary-number-theory.powers-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.archimedean-property-rational-numbers
open import elementary-number-theory.arithmetic-sequences-positive-rational-numbers
open import elementary-number-theory.bernoullis-inequality-positive-rational-numbers
open import elementary-number-theory.distance-rational-numbers
open import elementary-number-theory.geometric-sequences-positive-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-positive-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications

open import group-theory.multiples-of-elements-abelian-groups
open import group-theory.powers-of-elements-groups

open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.rational-sequences-approximating-zero

open import order-theory.posets
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="a positive rational number to a natural number power" Agda=power-ℚ⁺}}
on the [positive](elementary-number-theory.positive-rational-numbers.md)
[rational numbers](elementary-number-theory.rational-numbers.md) is the
operation `n x ↦ xⁿ`, which is defined by
[iteratively](foundation.iterating-functions.md) multiplying `x` with itself `n`
times. This file covers the case where `n` is a
[natural number](elementary-number-theory.natural-numbers.md).

## Definition

```agda
power-ℚ⁺ : ℕ → ℚ⁺ → ℚ⁺
power-ℚ⁺ = power-Group group-mul-ℚ⁺

rational-power-ℚ⁺ : ℕ → ℚ⁺ → ℚ
rational-power-ℚ⁺ n q = rational-ℚ⁺ (power-ℚ⁺ n q)
```

## Properties

### `1ⁿ = 1`

```agda
power-one-ℚ⁺ : (n : ℕ) → power-ℚ⁺ n one-ℚ⁺ ＝ one-ℚ⁺
power-one-ℚ⁺ = power-unit-Group group-mul-ℚ⁺
```

### `qⁿ⁺¹ = qⁿq`

```agda
power-succ-ℚ⁺ : (n : ℕ) (q : ℚ⁺) → power-ℚ⁺ (succ-ℕ n) q ＝ power-ℚ⁺ n q *ℚ⁺ q
power-succ-ℚ⁺ = power-succ-Group group-mul-ℚ⁺
```

### `qⁿ = qqⁿ`

```agda
power-succ-ℚ⁺' : (n : ℕ) (q : ℚ⁺) → power-ℚ⁺ (succ-ℕ n) q ＝ q *ℚ⁺ power-ℚ⁺ n q
power-succ-ℚ⁺' = power-succ-Group' group-mul-ℚ⁺
```

### `qᵐ⁺ⁿ = qᵐqⁿ`

```agda
distributive-power-add-ℚ⁺ :
  (m n : ℕ) (q : ℚ⁺) → power-ℚ⁺ (m +ℕ n) q ＝ power-ℚ⁺ m q *ℚ⁺ power-ℚ⁺ n q
distributive-power-add-ℚ⁺ m n _ = distributive-power-add-Group group-mul-ℚ⁺ m n
```

### `(pq)ⁿ=pⁿqⁿ`

```agda
left-distributive-power-mul-ℚ⁺ :
  (n : ℕ) (p q : ℚ⁺) → power-ℚ⁺ n (p *ℚ⁺ q) ＝ power-ℚ⁺ n p *ℚ⁺ power-ℚ⁺ n q
left-distributive-power-mul-ℚ⁺ n p q =
  left-distributive-multiple-add-Ab abelian-group-mul-ℚ⁺ n
```

### `pᵐⁿ = (pᵐ)ⁿ`

```agda
power-mul-ℚ⁺ :
  (m n : ℕ) (q : ℚ⁺) → power-ℚ⁺ (m *ℕ n) q ＝ power-ℚ⁺ n (power-ℚ⁺ m q)
power-mul-ℚ⁺ m n q = power-mul-Group group-mul-ℚ⁺ m n
```

### If `p` and `q` are positive rational numbers with `p < q` and `n` is nonzero, then `pⁿ < qⁿ`

```agda
abstract
  preserves-le-power-ℚ⁺ :
    (n : ℕ) → (p q : ℚ⁺) → le-ℚ⁺ p q → is-nonzero-ℕ n →
    le-ℚ⁺ (power-ℚ⁺ n p) (power-ℚ⁺ n q)
  preserves-le-power-ℚ⁺ 0 p q p<q H = ex-falso (H refl)
  preserves-le-power-ℚ⁺ 1 p q p<q _ = p<q
  preserves-le-power-ℚ⁺ (succ-ℕ n@(succ-ℕ _)) p q p<q _ =
    transitive-le-ℚ⁺
      ( power-ℚ⁺ (succ-ℕ n) p)
      ( power-ℚ⁺ n p *ℚ⁺ q)
      ( power-ℚ⁺ (succ-ℕ n) q)
      ( preserves-le-right-mul-ℚ⁺ q _ _
        ( preserves-le-power-ℚ⁺ n p q p<q (is-nonzero-succ-ℕ _)))
      ( preserves-le-left-mul-ℚ⁺ (power-ℚ⁺ n p) _ _ p<q)
```

### If `p` and `q` are positive rational numbers with `p ≤ q`, then `pⁿ ≤ qⁿ`

```agda
abstract
  preserves-leq-power-ℚ⁺ :
    (n : ℕ) (p q : ℚ⁺) → leq-ℚ⁺ p q → leq-ℚ⁺ (power-ℚ⁺ n p) (power-ℚ⁺ n q)
  preserves-leq-power-ℚ⁺ 0 _ _ _ = refl-leq-ℚ one-ℚ
  preserves-leq-power-ℚ⁺ 1 p q p≤q = p≤q
  preserves-leq-power-ℚ⁺ (succ-ℕ n@(succ-ℕ _)) p q p≤q =
    transitive-leq-ℚ⁺
      ( power-ℚ⁺ (succ-ℕ n) p)
      ( power-ℚ⁺ n p *ℚ⁺ q)
      ( power-ℚ⁺ (succ-ℕ n) q)
      ( preserves-leq-right-mul-ℚ⁺ q _ _ (preserves-leq-power-ℚ⁺ n p q p≤q))
      ( preserves-leq-left-mul-ℚ⁺ (power-ℚ⁺ n p) _ _ p≤q)
```

### For any positive rational `ε`, `(1 + ε)ⁿ` grows without bound

```agda
abstract
  bound-unbounded-power-one-plus-ℚ⁺ :
    (ε : ℚ⁺) (b : ℚ) →
    Σ ℕ (λ n → le-ℚ b (rational-ℚ⁺ (power-ℚ⁺ n (one-ℚ⁺ +ℚ⁺ ε))))
  bound-unbounded-power-one-plus-ℚ⁺ ε⁺@(ε , is-pos-ε) b =
    let
      (n , b<nε) = bound-archimedean-property-ℚ ε b is-pos-ε
    in
      ( n ,
        transitive-le-ℚ _ _ _
          ( concatenate-le-leq-ℚ _ _ _
            ( le-left-add-rational-ℚ⁺ _ one-ℚ⁺)
            ( binary-tr
              ( leq-ℚ)
              ( inv (compute-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ ε⁺ n))
              ( ap
                ( rational-ℚ⁺)
                ( equational-reasoning
                  seq-standard-geometric-sequence-ℚ⁺
                      ( one-ℚ⁺)
                      ( one-ℚ⁺ +ℚ⁺ ε⁺)
                      ( n)
                  ＝ one-ℚ⁺ *ℚ⁺ power-ℚ⁺ n (one-ℚ⁺ +ℚ⁺ ε⁺)
                    by
                      inv
                        ( compute-standard-geometric-sequence-ℚ⁺
                          ( one-ℚ⁺)
                          ( one-ℚ⁺ +ℚ⁺ ε⁺)
                          ( n))
                  ＝ power-ℚ⁺ n (one-ℚ⁺ +ℚ⁺ ε⁺)
                    by left-unit-law-mul-ℚ⁺ _))
              ( bernoullis-inequality-ℚ⁺ ε⁺ n)))
          ( b<nε))

  unbounded-power-one-plus-ℚ⁺ :
    (ε : ℚ⁺) (b : ℚ) →
    exists ℕ (λ n → le-ℚ-Prop b (rational-ℚ⁺ (power-ℚ⁺ n (one-ℚ⁺ +ℚ⁺ ε))))
  unbounded-power-one-plus-ℚ⁺ ε b =
    unit-trunc-Prop (bound-unbounded-power-one-plus-ℚ⁺ ε b)
```

### If `q` is greater than one, `qⁿ` grows without bound

```agda
abstract
  bound-unbounded-power-greater-than-one-ℚ⁺ :
    (q : ℚ⁺) (b : ℚ) → le-ℚ⁺ one-ℚ⁺ q →
    Σ ℕ (λ n → le-ℚ b (rational-ℚ⁺ (power-ℚ⁺ n q)))
  bound-unbounded-power-greater-than-one-ℚ⁺ q⁺@(q , _) b 1<q =
    let
      (n , b<⟨1+q-1⟩ⁿ) =
        bound-unbounded-power-one-plus-ℚ⁺ (positive-diff-le-ℚ 1<q) b
    in
      ( n ,
        tr
          ( le-ℚ b)
          ( ap
            ( rational-ℚ⁺ ∘ power-ℚ⁺ n)
            ( eq-ℚ⁺ (is-identity-right-conjugation-add-ℚ one-ℚ q)))
          ( b<⟨1+q-1⟩ⁿ))

  unbounded-power-greater-than-one-ℚ⁺ :
    (q : ℚ⁺) (b : ℚ) → le-ℚ⁺ one-ℚ⁺ q →
    exists ℕ (λ n → le-ℚ-Prop b (rational-ℚ⁺ (power-ℚ⁺ n q)))
  unbounded-power-greater-than-one-ℚ⁺ q b 1<q =
    unit-trunc-Prop (bound-unbounded-power-greater-than-one-ℚ⁺ q b 1<q)
```

### If `ε` is a positive rational number less than one, `εⁿ` becomes arbitrarily small

```agda
abstract
  bound-arbitrarily-small-power-le-one-ℚ⁺ :
    (ε δ : ℚ⁺) → le-ℚ⁺ ε one-ℚ⁺ →
    Σ ℕ (λ n → le-ℚ⁺ (power-ℚ⁺ n ε) δ)
  bound-arbitrarily-small-power-le-one-ℚ⁺ ε δ ε<1 =
    let
      1/δ = inv-ℚ⁺ δ
      1/ε = inv-ℚ⁺ ε
      1<1/ε =
        tr
          ( λ q → le-ℚ⁺ q 1/ε)
          ( inv-one-ℚ⁺)
          ( inv-le-ℚ⁺ ε one-ℚ⁺ ε<1)
      (n , 1/δ<⟨1/ε⟩ⁿ) =
        bound-unbounded-power-greater-than-one-ℚ⁺ 1/ε (rational-ℚ⁺ 1/δ) 1<1/ε
    in
      ( n ,
        binary-tr
          ( le-ℚ⁺)
          ( equational-reasoning
            inv-ℚ⁺ (power-ℚ⁺ n 1/ε)
            ＝ inv-ℚ⁺ (inv-ℚ⁺ (power-ℚ⁺ n ε))
              by ap inv-ℚ⁺ (power-inv-Group group-mul-ℚ⁺ n ε)
            ＝ power-ℚ⁺ n ε
              by inv-inv-ℚ⁺ (power-ℚ⁺ n ε))
          ( inv-inv-ℚ⁺ δ)
          ( inv-le-ℚ⁺ 1/δ (power-ℚ⁺ n 1/ε) 1/δ<⟨1/ε⟩ⁿ))

  arbitrarily-small-power-le-one-ℚ⁺ :
    (ε δ : ℚ⁺) → le-ℚ⁺ ε one-ℚ⁺ →
    exists ℕ (λ n → le-prop-ℚ⁺ (power-ℚ⁺ n ε) δ)
  arbitrarily-small-power-le-one-ℚ⁺ ε δ 1<ε =
    unit-trunc-Prop (bound-arbitrarily-small-power-le-one-ℚ⁺ ε δ 1<ε)
```

### If `ε` is a positive rational number less than or equal to 1 and `m ≤ n`, then `εⁿ ≤ εᵐ`

```agda
abstract
  leq-power-leq-one-ℚ⁺ :
    (ε : ℚ⁺) → leq-ℚ⁺ ε one-ℚ⁺ → (m n : ℕ) → leq-ℕ m n →
    leq-ℚ⁺ (power-ℚ⁺ n ε) (power-ℚ⁺ m ε)
  leq-power-leq-one-ℚ⁺ ε ε≤1 m n m≤n =
    let
      (k , k+m=n) = subtraction-leq-ℕ m n m≤n
      open inequality-reasoning-Poset ℚ-Poset
    in
      chain-of-inequalities
        rational-power-ℚ⁺ n ε
        ≤ rational-power-ℚ⁺ (k +ℕ m) ε
          by leq-eq-ℚ⁺ (ap (λ x → power-ℚ⁺ x ε) (inv k+m=n))
        ≤ rational-power-ℚ⁺ k ε *ℚ rational-power-ℚ⁺ m ε
          by leq-eq-ℚ⁺ (distributive-power-add-ℚ⁺ k m ε)
        ≤ rational-power-ℚ⁺ k one-ℚ⁺ *ℚ rational-power-ℚ⁺ m ε
          by
            preserves-leq-right-mul-ℚ⁺
              ( power-ℚ⁺ m ε)
              ( _)
              ( _)
              ( preserves-leq-power-ℚ⁺ k ε one-ℚ⁺ ε≤1)
        ≤ one-ℚ *ℚ rational-power-ℚ⁺ m ε
          by leq-eq-ℚ (ap-mul-ℚ (ap rational-ℚ⁺ (power-one-ℚ⁺ k)) refl)
        ≤ rational-power-ℚ⁺ m ε
          by leq-eq-ℚ (left-unit-law-mul-ℚ _)
```

### If `ε` is a positive rational number less than 1, `εⁿ` approaches 0

```agda
abstract
  is-zero-limit-power-le-one-ℚ⁺ :
    (ε : ℚ⁺) → le-ℚ⁺ ε one-ℚ⁺ →
    is-zero-limit-sequence-ℚ (λ n → rational-ℚ⁺ (power-ℚ⁺ n ε))
  is-zero-limit-power-le-one-ℚ⁺ ε ε<1 =
    is-limit-bound-modulus-sequence-Metric-Space
      ( metric-space-ℚ)
      ( _)
      ( zero-ℚ)
      ( λ δ →
        let
          (m , εᵐ<δ) =
            bound-arbitrarily-small-power-le-one-ℚ⁺ ε δ ε<1
          open inequality-reasoning-Poset ℚ-Poset
        in
          ( m ,
            λ n m≤n →
              neighborhood-leq-dist-ℚ
                ( δ)
                ( rational-power-ℚ⁺ n ε)
                ( zero-ℚ)
                ( chain-of-inequalities
                  rational-dist-ℚ (rational-ℚ⁺ (power-ℚ⁺ n ε)) zero-ℚ
                  ≤ rational-abs-ℚ (rational-ℚ⁺ (power-ℚ⁺ n ε))
                    by
                      leq-eq-ℚ (ap rational-ℚ⁰⁺ (right-zero-law-dist-ℚ _))
                  ≤ rational-ℚ⁺ (power-ℚ⁺ n ε)
                    by
                      leq-eq-ℚ
                        ( ap rational-ℚ⁰⁺
                          ( abs-rational-ℚ⁰⁺ (nonnegative-ℚ⁺ (power-ℚ⁺ n ε))))
                  ≤ rational-ℚ⁺ (power-ℚ⁺ m ε)
                    by leq-power-leq-one-ℚ⁺ ε (leq-le-ℚ ε<1) m n m≤n
                  ≤ rational-ℚ⁺ δ
                    by leq-le-ℚ εᵐ<δ)))
```

## See also

- [Powers of elements of a group](group-theory.powers-of-elements-groups.md)
