# Cauchy filters on the rational numbers

```agda
module real-numbers.cauchy-filters-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.distance-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
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
open import foundation.dependent-products-propositions
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-filters-metric-spaces
open import metric-spaces.complete-metric-space-of-cauchy-filters-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.expansive-maps-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.local-rational-neighborhood-subtypes-pseudometric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.proper-rational-neighborhood-subtypes
open import metric-spaces.rational-neighborhood-subtypes
open import metric-spaces.saturated-rational-neighborhood-subtypes
open import metric-spaces.short-maps-metric-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.cauchy-completeness-dedekind-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.dense-subsets-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-approximates-of-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The
[metric space of Cauchy filters](metric-spaces.metric-space-of-cauchy-filters-pseudometric-spaces.md)
on the
[metric space of rational numbers](metric-spaces.metric-space-of-rational-numbers.md)
is [isometrically equivalent](metric-spaces.equality-of-metric-spaces.md) to the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

Any [real number](real-numbers.dedekind-real-numbers.md) `x : ℝ` defines a
[Cauchy filter](metric-spaces.cauchy-filters-metric-spaces.md) on
[`ℚ`](elementary-number-theory.rational-numbers.md) via:

```text
  Vₓ ε q = neighborhood-ℝ ε x (ι q)
```

where `ι` is the canonical embedding of
[rational real numbers](real-numbers.rational-real-numbers.md).

Conversely, a Cauchy filter `V` on `ℚ` defines a
[real number](real-numbers.dedekind-real-numbers.md) as the disjoint located
pair of [lower](real-numbers.lower-dedekind-real-numbers.md) and
[upper](real-numbers.upper-dedekind-real-numbers.md) `(L , U)` given by:

- `L p = ∃ (ℚ⁺ × ℚ) (λ ε q → (p + ε < q) ∧ (V ε q))`; i.e. `L p` holds iff `p`
  is `ε`-lower than some `V ε`-point;
- `U q = ∃ (ℚ⁺ × ℚ) (λ ε p → (p + ε < q) ∧ (V ε p))`; i.e. `U q` holds iff `q`
  is `ε`-greater than some `V ε`-point.

These maps

- `real-cauchy-filter-ℚ : cauchy-filter-ℚ l → ℝ l`
- `cauchy-filter-ℚ-ℝ : ℝ l → cauchy-filter-ℚ`

are [isometries](metric-spaces.isometries-metric-spaces.md) and satisfy

```text
  real-cauchy-filter-ℚ ∘ cauchy-filter-ℚ-ℝ ~ id
```

hence induce an isometric equivalence between Cauchy filters on rational numbers
and Dedekind real numbers.

## Definitions

### The complete metric space of Cauchy filters of rational numbers

```agda
module _
  (l : Level)
  where

  complete-metric-space-cauchy-filter-ℚ :
    Complete-Metric-Space (lsuc l) l
  complete-metric-space-cauchy-filter-ℚ =
    complete-metric-space-cauchy-filter-Pseudometric-Space
      ( l)
      ( pseudometric-space-ℚ)

  metric-space-cauchy-filter-ℚ : Metric-Space (lsuc l) l
  metric-space-cauchy-filter-ℚ =
    metric-space-Complete-Metric-Space
      complete-metric-space-cauchy-filter-ℚ

  cauchy-filter-ℚ : UU (lsuc l)
  cauchy-filter-ℚ = type-Metric-Space metric-space-cauchy-filter-ℚ
```

### Components of Cauchy filters on the rational numbers

```agda
module _
  {l : Level} (V : cauchy-filter-ℚ l)
  where

  neighborhood-subtype-cauchy-filter-ℚ : ℚ⁺ → ℚ → Prop l
  neighborhood-subtype-cauchy-filter-ℚ =
    neighborhood-subtype-cauchy-filter-Metric-Space metric-space-ℚ V

  is-in-cauchy-filter-ℚ : ℚ⁺ → ℚ → UU l
  is-in-cauchy-filter-ℚ =
    is-in-cauchy-filter-Metric-Space metric-space-ℚ V

  is-proper-cauchy-filter-ℚ :
    (ε : ℚ⁺) → exists ℚ (neighborhood-subtype-cauchy-filter-ℚ ε)
  is-proper-cauchy-filter-ℚ =
    is-proper-cauchy-filter-Metric-Space metric-space-ℚ V

  is-saturated-cauchy-filter-ℚ :
    (ε : ℚ⁺) (p : ℚ) →
    ((μ : ℚ⁺) → is-in-cauchy-filter-ℚ (ε +ℚ⁺ μ) p) →
    is-in-cauchy-filter-ℚ ε p
  is-saturated-cauchy-filter-ℚ ε p =
    is-saturated-cauchy-filter-Metric-Space metric-space-ℚ V (ε , p)

  is-bounded-cauchy-filter-ℚ :
    (ε δ : ℚ⁺) (p q : ℚ) →
    is-in-cauchy-filter-ℚ ε p →
    is-in-cauchy-filter-ℚ δ q →
    neighborhood-ℚ (ε +ℚ⁺ δ) p q
  is-bounded-cauchy-filter-ℚ =
    is-bounded-cauchy-filter-Metric-Space metric-space-ℚ V

  is-enclosing-cauchy-filter-ℚ :
    (ε δ : ℚ⁺) (p q : ℚ) →
    is-in-cauchy-filter-ℚ ε p →
    neighborhood-ℚ δ p q →
    is-in-cauchy-filter-ℚ (ε +ℚ⁺ δ) q
  is-enclosing-cauchy-filter-ℚ =
    is-enclosing-cauchy-filter-Metric-Space metric-space-ℚ V

  is-monotonic-cauchy-filter-ℚ :
    (p : ℚ) (ε δ : ℚ⁺) →
    le-ℚ⁺ ε δ →
    is-in-cauchy-filter-ℚ ε p →
    is-in-cauchy-filter-ℚ δ p
  is-monotonic-cauchy-filter-ℚ =
    is-monotonic-cauchy-filter-Metric-Space metric-space-ℚ V
```

### Cauchy filter on the rational numbers induced by a Dedekind real number

```agda
module _
  {l : Level} (x : ℝ l)
  where

  neighborhood-subtype-ℚ-ℝ : Rational-Neighborhood-Subtype l ℚ
  neighborhood-subtype-ℚ-ℝ ε p =
    neighborhood-prop-ℝ l ε x (raise-real-ℚ l p)

  is-in-neighborhood-subtype-ℚ-ℝ : ℚ⁺ → ℚ → UU l
  is-in-neighborhood-subtype-ℚ-ℝ =
    is-in-Rational-Neighborhood-Subtype neighborhood-subtype-ℚ-ℝ

  is-saturated-neighborhood-subtype-ℚ-ℝ :
    is-saturated-Rational-Neighborhood-Subtype neighborhood-subtype-ℚ-ℝ
  is-saturated-neighborhood-subtype-ℚ-ℝ (ε , p) =
    is-saturated-neighborhood-ℝ ε x (raise-real-ℚ l p)

  is-bounded-neighborhood-subtype-ℚ-ℝ :
    (ε δ : ℚ⁺) (p q : ℚ) →
    is-bounded-neighborhood-subtype-Pseudometric-Space
      ( pseudometric-space-ℚ)
      ( neighborhood-subtype-ℚ-ℝ)
      ( ε)
      ( δ)
      ( p)
      ( q)
  is-bounded-neighborhood-subtype-ℚ-ℝ ε δ p q (Up , Uq) =
    reflects-neighborhoods-map-isometry-Metric-Space
      ( metric-space-ℚ)
      ( metric-space-ℝ l)
      ( isometry-raise-real-ℚ l)
      ( ε +ℚ⁺ δ)
      ( p)
      ( q)
      ( is-triangular-neighborhood-ℝ
        ( raise-real-ℚ l p)
        ( x)
        ( raise-real-ℚ l q)
        ( ε)
        ( δ)
        ( Uq)
        ( is-symmetric-neighborhood-ℝ ε x (raise-real-ℚ l p) Up))

  is-enclosing-neighborhood-subtype-ℚ-ℝ :
    (ε δ : ℚ⁺) (p q : ℚ) →
    is-enclosing-neighborhood-subtype-Pseudometric-Space
      ( pseudometric-space-ℚ)
      ( neighborhood-subtype-ℚ-ℝ)
      ( ε)
      ( δ)
      ( p)
      ( q)
  is-enclosing-neighborhood-subtype-ℚ-ℝ ε δ p q (Up , Npq) =
    is-triangular-neighborhood-ℝ
      ( x)
      ( raise-real-ℚ l p)
      ( raise-real-ℚ l q)
      ( ε)
      ( δ)
      ( preserves-neighborhoods-map-isometry-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℝ l)
        ( isometry-raise-real-ℚ l)
        ( δ)
        ( p)
        ( q)
        ( Npq))
      ( Up)

  is-local-neighborhood-subtype-ℚ-ℝ :
    is-local-neighborhood-subtype-Pseudometric-Space
      ( pseudometric-space-ℚ)
      ( neighborhood-subtype-ℚ-ℝ)
  is-local-neighborhood-subtype-ℚ-ℝ (ε , δ , x , y) =
    ( is-bounded-neighborhood-subtype-ℚ-ℝ ε δ x y ,
      is-enclosing-neighborhood-subtype-ℚ-ℝ ε δ x y)

  cauchy-filter-ℚ-ℝ : cauchy-filter-ℚ l
  cauchy-filter-ℚ-ℝ =
    ( neighborhood-subtype-ℚ-ℝ ,
      exists-rational-approximate-ℝ x ,
      is-saturated-neighborhood-subtype-ℚ-ℝ ,
      is-local-neighborhood-subtype-ℚ-ℝ)
```

### Lower real number induced by a Cauchy filter on the rational numbers

```agda
module _
  {l : Level} (V : cauchy-filter-ℚ l)
  where

  lower-cut-cauchy-filter-ℚ : subtype l ℚ
  lower-cut-cauchy-filter-ℚ p =
    ∃ ( ℚ⁺ × ℚ)
      ( λ ( ε , q) →
        ( ( le-ℚ-Prop (p +ℚ rational-ℚ⁺ ε) q)) ∧
          ( neighborhood-subtype-cauchy-filter-ℚ V ε q))

  is-in-lower-cut-cauchy-filter-ℚ : ℚ → UU l
  is-in-lower-cut-cauchy-filter-ℚ = is-in-subtype lower-cut-cauchy-filter-ℚ

  is-inhabited-lower-cut-cauchy-filter-ℚ :
    is-inhabited-subtype lower-cut-cauchy-filter-ℚ
  is-inhabited-lower-cut-cauchy-filter-ℚ =
    let
      open
        do-syntax-trunc-Prop (∃ ℚ lower-cut-cauchy-filter-ℚ)
    in do
      ε ← is-inhabited-ℚ⁺
      (q , Vq) ← is-proper-cauchy-filter-ℚ V ε
      (p , p<q-ε) ← exists-lesser-ℚ (q -ℚ rational-ℚ⁺ ε)
      let
        p+ε<q : le-ℚ (p +ℚ rational-ℚ⁺ ε) q
        p+ε<q =
          le-transpose-right-diff-ℚ
            ( p)
            ( q)
            ( rational-ℚ⁺ ε)
            ( p<q-ε)

      intro-exists p (intro-exists (ε , q) (p+ε<q , Vq))

  is-upper-open-lower-cut-cauchy-filter-ℚ :
    (p : ℚ) →
    is-in-lower-cut-cauchy-filter-ℚ p →
    exists
      ( ℚ)
      ( λ q → le-ℚ-Prop p q ∧ lower-cut-cauchy-filter-ℚ q)
  is-upper-open-lower-cut-cauchy-filter-ℚ p Lp =
    let
      open
        do-syntax-trunc-Prop
          ( ∃ ( ℚ)
              ( λ q → le-ℚ-Prop p q ∧ lower-cut-cauchy-filter-ℚ q))
    in do
      ((ε , r) , (p+ε<r , Ur)) ← Lp
      (q , p+ε<q , q<r) ← dense-le-ℚ p+ε<r

      intro-exists
        ( q -ℚ rational-ℚ⁺ ε)
        ( ( le-transpose-left-add-ℚ p (rational-ℚ⁺ ε) q p+ε<q) ,
          ( intro-exists
            ( ε , r)
            ( ( le-transpose-right-diff-ℚ
                ( q -ℚ rational-ℚ⁺ ε)
                ( r)
                ( rational-ℚ⁺ ε)
                ( preserves-le-left-add-ℚ
                  ( neg-ℚ (rational-ℚ⁺ ε))
                  ( q)
                  ( r)
                  ( q<r))) ,
              ( Ur))))

  is-lower-subset-lower-cut-cauchy-filter-ℚ :
    (p q : ℚ) →
    le-ℚ p q →
    is-in-lower-cut-cauchy-filter-ℚ q →
    is-in-lower-cut-cauchy-filter-ℚ p
  is-lower-subset-lower-cut-cauchy-filter-ℚ p q p<q Lq =
    let
      open
        do-syntax-trunc-Prop (lower-cut-cauchy-filter-ℚ p)
    in do
      ( (ε , r) , (q+ε<r , Ur)) ← Lq
      intro-exists
        ( ε , r)
        ( ( transitive-le-ℚ
            ( p +ℚ rational-ℚ⁺ ε)
            ( q +ℚ rational-ℚ⁺ ε)
            ( r)
            ( q+ε<r)
            ( preserves-le-left-add-ℚ (rational-ℚ⁺ ε) p q p<q)) ,
          ( Ur))

  is-dedekind-lower-cut-cauchy-filter-ℚ :
    is-lower-dedekind-cut lower-cut-cauchy-filter-ℚ
  is-dedekind-lower-cut-cauchy-filter-ℚ =
    ( is-inhabited-lower-cut-cauchy-filter-ℚ ,
      λ p →
        ( is-upper-open-lower-cut-cauchy-filter-ℚ p ,
          elim-exists
            ( lower-cut-cauchy-filter-ℚ p)
            ( λ q (p<q , Lq) →
              is-lower-subset-lower-cut-cauchy-filter-ℚ p q p<q Lq)))

  lower-real-cauchy-filter-ℚ : lower-ℝ l
  lower-real-cauchy-filter-ℚ =
    ( lower-cut-cauchy-filter-ℚ , is-dedekind-lower-cut-cauchy-filter-ℚ)
```

### Upper real number induced by a Cauchy filter on the rational numbers

```agda
module _
  {l : Level} (V : cauchy-filter-ℚ l)
  where

  upper-cut-cauchy-filter-ℚ : subtype l ℚ
  upper-cut-cauchy-filter-ℚ q =
    ∃ ( ℚ⁺ × ℚ)
      ( λ (ε , p) →
        ( ( le-ℚ-Prop (p +ℚ rational-ℚ⁺ ε) q)) ∧
          ( neighborhood-subtype-cauchy-filter-ℚ V ε p))

  is-in-upper-cut-cauchy-filter-ℚ : ℚ → UU l
  is-in-upper-cut-cauchy-filter-ℚ = is-in-subtype upper-cut-cauchy-filter-ℚ

  is-inhabited-upper-cut-cauchy-filter-ℚ :
    is-inhabited-subtype upper-cut-cauchy-filter-ℚ
  is-inhabited-upper-cut-cauchy-filter-ℚ =
    let
      open do-syntax-trunc-Prop (∃ ℚ upper-cut-cauchy-filter-ℚ)
    in do
      ε ← is-inhabited-ℚ⁺
      (p , Vp) ← is-proper-cauchy-filter-ℚ V ε
      (q , p+ε<q) ← exists-greater-ℚ (p +ℚ rational-ℚ⁺ ε)
      intro-exists q (intro-exists (ε , p) (p+ε<q , Vp))

  is-lower-open-upper-cut-cauchy-filter-ℚ :
    (q : ℚ) →
    is-in-upper-cut-cauchy-filter-ℚ q →
    exists
      ( ℚ)
      ( λ p → le-ℚ-Prop p q ∧ upper-cut-cauchy-filter-ℚ p)
  is-lower-open-upper-cut-cauchy-filter-ℚ q Uq =
    let
      open
        do-syntax-trunc-Prop
          ( ∃ ( ℚ)
              ( λ p → le-ℚ-Prop p q ∧ upper-cut-cauchy-filter-ℚ p))
    in do
      ((ε , r) , (r+ε<q , Ur)) ← Uq
      (p , r+ε<p , p<q) ← dense-le-ℚ r+ε<q
      intro-exists p (p<q , intro-exists (ε , r) (r+ε<p , Ur))

  is-upper-subset-upper-cut-cauchy-filter-ℚ :
    (p q : ℚ) →
    le-ℚ p q →
    is-in-upper-cut-cauchy-filter-ℚ p →
    is-in-upper-cut-cauchy-filter-ℚ q
  is-upper-subset-upper-cut-cauchy-filter-ℚ p q p<q Up =
    let
      open
        do-syntax-trunc-Prop
          ( upper-cut-cauchy-filter-ℚ q)
    in do
      ( (ε , r) , (r+ε<p , Ur)) ← Up
      intro-exists
        ( ε , r)
        ( transitive-le-ℚ (r +ℚ rational-ℚ⁺ ε) p q p<q r+ε<p , Ur)

  is-dedekind-upper-cut-cauchy-filter-ℚ :
    is-upper-dedekind-cut upper-cut-cauchy-filter-ℚ
  is-dedekind-upper-cut-cauchy-filter-ℚ =
    ( is-inhabited-upper-cut-cauchy-filter-ℚ ,
      λ q →
        ( is-lower-open-upper-cut-cauchy-filter-ℚ q ,
          elim-exists
            ( upper-cut-cauchy-filter-ℚ q)
            ( λ p (p<q , Up) →
              is-upper-subset-upper-cut-cauchy-filter-ℚ p q p<q Up)))

  upper-real-cauchy-filter-ℚ : upper-ℝ l
  upper-real-cauchy-filter-ℚ =
    ( upper-cut-cauchy-filter-ℚ , is-dedekind-upper-cut-cauchy-filter-ℚ)
```

### Dedekind real number induced by a Cauchy filter on the rational numbers

```agda
module _
  {l : Level} (V : cauchy-filter-ℚ l)
  where

  is-disjoint-lower-upper-cauchy-filter-ℚ :
    is-disjoint-lower-upper-ℝ
      ( lower-real-cauchy-filter-ℚ V)
      ( upper-real-cauchy-filter-ℚ V)
  is-disjoint-lower-upper-cauchy-filter-ℚ p (Lp , Up) =
    let
      open
        do-syntax-trunc-Prop empty-Prop
    in do
      ((α , q) , (p+α<q , Vq)) ← Lp
      ((β , r) , (r+β<p , Vr)) ← Up

      not-leq-le-ℚ
        ( rational-ℚ⁺ (α +ℚ⁺ β))
        ( diff-ℚ q r)
        ( le-transpose-left-add-ℚ
            ( rational-ℚ⁺ (α +ℚ⁺ β))
            ( r)
            ( q)
            ( tr
              ( λ z → le-ℚ z q)
              ( commutative-add-ℚ r (rational-ℚ⁺ (α +ℚ⁺ β)))
              ( transitive-le-ℚ
                ( r +ℚ rational-ℚ⁺ (α +ℚ⁺ β))
                ( p +ℚ rational-ℚ⁺ α)
                ( q)
                ( p+α<q)
                ( tr
                  ( λ z → le-ℚ z (p +ℚ rational-ℚ⁺ α))
                  ( associative-add-ℚ r (rational-ℚ⁺ β) (rational-ℚ⁺ α) ∙
                    ap
                      ( add-ℚ r)
                      ( commutative-add-ℚ (rational-ℚ⁺ β) (rational-ℚ⁺ α)))
                  ( preserves-le-left-add-ℚ
                    ( rational-ℚ⁺ α)
                    ( r +ℚ rational-ℚ⁺ β)
                    ( p)
                    ( r+β<p))))))
        ( transitive-leq-ℚ
            ( diff-ℚ q r)
            ( rational-dist-ℚ q r)
            ( rational-ℚ⁺ (α +ℚ⁺ β))
            ( leq-dist-neighborhood-ℚ
              ( α +ℚ⁺ β)
              ( q)
              ( r)
              ( is-bounded-cauchy-filter-ℚ V α β q r Vq Vr))
            ( leq-diff-dist-ℚ q r))

  is-located-lower-upper-cauchy-filter-ℚ :
    is-located-lower-upper-ℝ
      ( lower-real-cauchy-filter-ℚ V)
      ( upper-real-cauchy-filter-ℚ V)
  is-located-lower-upper-cauchy-filter-ℚ q r q<r =
    let
      ε : ℚ⁺
      ε = positive-diff-le-ℚ q<r

      open
        do-syntax-trunc-Prop
          ( (lower-cut-cauchy-filter-ℚ V q) ∨ (upper-cut-cauchy-filter-ℚ V r))
    in do
      (δ , δ+δ<ε) ← double-le-ℚ⁺ ε
      (p , Vp) ← is-proper-cauchy-filter-ℚ V δ

      let
        q+δ<r-δ : le-ℚ (q +ℚ rational-ℚ⁺ δ) (r -ℚ rational-ℚ⁺ δ)
        q+δ<r-δ =
          le-transpose-left-add-ℚ
            ( q +ℚ rational-ℚ⁺ δ)
            ( rational-ℚ⁺ δ)
            ( r)
            ( binary-tr
              ( le-ℚ)
              ( inv (associative-add-ℚ q (rational-ℚ⁺ δ) (rational-ℚ⁺ δ)))
              ( right-law-positive-diff-le-ℚ q<r)
              ( preserves-le-right-add-ℚ
                ( q)
                ( rational-ℚ⁺ (δ +ℚ⁺ δ))
                ( rational-ℚ⁺ ε)
                ( δ+δ<ε)))

      elim-disjunction
        ( (lower-cut-cauchy-filter-ℚ V q) ∨ (upper-cut-cauchy-filter-ℚ V r))
        ( λ q+δ<p → inl-disjunction (intro-exists (δ , p) (q+δ<p , Vp)))
        ( λ p<r-δ →
          inr-disjunction
            ( intro-exists
              ( δ , p)
              ( le-transpose-right-diff-ℚ p r (rational-ℚ⁺ δ) p<r-δ , Vp)))
        ( located-le-ℚ p (q +ℚ rational-ℚ⁺ δ) (r -ℚ rational-ℚ⁺ δ) q+δ<r-δ)

  is-dedekind-lower-upper-cauchy-filter-ℚ :
    is-dedekind-lower-upper-ℝ
      ( lower-real-cauchy-filter-ℚ V)
      ( upper-real-cauchy-filter-ℚ V)
  is-dedekind-lower-upper-cauchy-filter-ℚ =
    ( is-disjoint-lower-upper-cauchy-filter-ℚ ,
      is-located-lower-upper-cauchy-filter-ℚ)

  real-cauchy-filter-ℚ : ℝ l
  real-cauchy-filter-ℚ =
    ( lower-real-cauchy-filter-ℚ V ,
      upper-real-cauchy-filter-ℚ V ,
      is-dedekind-lower-upper-cauchy-filter-ℚ)
```

## Properties

### Rational points of a Cauchy filter are neighbors of its real image

```agda
module _
  {l : Level} (V : cauchy-filter-ℚ l) (ε : ℚ⁺) (r : ℚ)
  (Vr : is-in-cauchy-filter-ℚ V ε r)
  where abstract

  opaque
    unfolding leq-ℝ leq-ℝ' real-ℚ

    leq-real-is-in-cauchy-filter-ℚ :
      leq-ℝ (real-ℚ (r -ℚ rational-ℚ⁺ ε)) (real-cauchy-filter-ℚ V)
    leq-real-is-in-cauchy-filter-ℚ p Hp =
      intro-exists
        ( ε , r)
        ( ( le-transpose-right-diff-ℚ
            ( p)
            ( r)
            ( rational-ℚ⁺ ε)
            ( Hp)) ,
          ( Vr))

    leq'-real-is-in-cauchy-filter-ℚ :
      leq-ℝ' (real-cauchy-filter-ℚ V) (real-ℚ (r +ℚ rational-ℚ⁺ ε))
    leq'-real-is-in-cauchy-filter-ℚ q Hq =
      intro-exists (ε , r) (Hq , Vr)

  is-in-neighborhood-real-is-in-cauchy-filter-ℚ :
    neighborhood-ℝ l ε (real-cauchy-filter-ℚ V) (raise-real-ℚ l r)
  is-in-neighborhood-real-is-in-cauchy-filter-ℚ =
    neighborhood-real-bound-each-leq-ℝ
      ( ε)
      ( real-cauchy-filter-ℚ V)
      ( raise-real-ℚ l r)
      ( preserves-leq-right-sim-ℝ
        ( lemma-sim-r+ε)
        ( leq-leq'-ℝ
          ( real-cauchy-filter-ℚ V)
          ( real-ℚ (r +ℚ rational-ℚ⁺ ε))
          ( leq'-real-is-in-cauchy-filter-ℚ)))
      ( leq-transpose-left-diff-ℝ
        ( raise-real-ℚ l r)
        ( real-ℚ⁺ ε)
        ( real-cauchy-filter-ℚ V)
        ( preserves-leq-left-sim-ℝ
          ( lemma-sim-r-ε)
          ( leq-real-is-in-cauchy-filter-ℚ)))
      where

      lemma-sim-r-ε :
        sim-ℝ (real-ℚ (r -ℚ rational-ℚ⁺ ε)) (raise-real-ℚ l r -ℝ real-ℚ⁺ ε)
      lemma-sim-r-ε =
        similarity-reasoning-ℝ
          real-ℚ (r -ℚ rational-ℚ⁺ ε)
          ~ℝ (real-ℚ r) -ℝ (real-ℚ⁺ ε)
            by sim-eq-ℝ (inv (diff-real-ℚ r (rational-ℚ⁺ ε)))
          ~ℝ raise-real-ℚ l r -ℝ real-ℚ⁺ ε
            by
              preserves-sim-right-add-ℝ
                ( neg-ℝ (real-ℚ⁺ ε))
                ( real-ℚ r)
                ( raise-real-ℚ l r)
                ( sim-raise-ℝ l (real-ℚ r))

      lemma-sim-r+ε :
        sim-ℝ (real-ℚ (r +ℚ rational-ℚ⁺ ε)) (raise-real-ℚ l r +ℝ real-ℚ⁺ ε)
      lemma-sim-r+ε =
        similarity-reasoning-ℝ
          real-ℚ (r +ℚ rational-ℚ⁺ ε)
          ~ℝ (real-ℚ r) +ℝ (real-ℚ⁺ ε)
            by sim-eq-ℝ (inv (add-real-ℚ r (rational-ℚ⁺ ε)))
          ~ℝ raise-real-ℚ l r +ℝ real-ℚ⁺ ε
            by
              preserves-sim-right-add-ℝ
                ( real-ℚ⁺ ε)
                ( real-ℚ r)
                ( raise-real-ℚ l r)
                ( sim-raise-ℝ l (real-ℚ r))
```

### The map real-cauchy-filter-ℚ is short

```agda
module _
  {l : Level}
  where abstract

  is-short-map-real-cauchy-filter-ℚ :
    is-short-map-Metric-Space
      ( metric-space-cauchy-filter-ℚ l)
      ( metric-space-ℝ l)
      ( real-cauchy-filter-ℚ)
  is-short-map-real-cauchy-filter-ℚ d x y Nxy =
    is-saturated-neighborhood-ℝ
      ( d)
      ( real-cauchy-filter-ℚ x)
      ( real-cauchy-filter-ℚ y)
      ( saturate-real-cauchy-Nxy)
    where

    saturate-real-cauchy-Nxy :
      (μ : ℚ⁺) →
      neighborhood-Metric-Space
        ( metric-space-ℝ l)
        ( d +ℚ⁺ μ)
        ( real-cauchy-filter-ℚ x)
        ( real-cauchy-filter-ℚ y)
    saturate-real-cauchy-Nxy μ =
      let
        open
          do-syntax-trunc-Prop
            ( neighborhood-prop-ℝ
              ( l)
              ( d +ℚ⁺ μ)
              ( real-cauchy-filter-ℚ x)
              ( real-cauchy-filter-ℚ y))
      in do
        (ε , ε+ε<μ) ← double-le-ℚ⁺ μ
        (δ , δ+δ<ε) ← double-le-ℚ⁺ ε
        (p , xp) ← is-proper-cauchy-filter-ℚ x δ
        (q , yq) ← is-proper-cauchy-filter-ℚ y δ

        let
          N-real-xy :
            neighborhood-ℝ
              ( l)
              ( δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d) +ℚ⁺ δ)
              ( real-cauchy-filter-ℚ x)
              ( real-cauchy-filter-ℚ y)
          N-real-xy =
            is-triangular-neighborhood-ℝ
              ( real-cauchy-filter-ℚ x)
              ( raise-real-ℚ l q)
              ( real-cauchy-filter-ℚ y)
              ( δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d))
              ( δ)
              ( is-symmetric-neighborhood-ℝ
                ( δ)
                ( real-cauchy-filter-ℚ y)
                ( raise-real-ℚ l q)
                ( is-in-neighborhood-real-is-in-cauchy-filter-ℚ
                  ( y)
                  ( δ)
                  ( q)
                  ( yq)))
              ( is-triangular-neighborhood-ℝ
                ( real-cauchy-filter-ℚ x)
                ( raise-real-ℚ l p)
                ( raise-real-ℚ l q)
                ( δ)
                ( δ +ℚ⁺ δ +ℚ⁺ d)
                ( preserves-neighborhoods-map-isometry-Metric-Space
                  ( metric-space-ℚ)
                  ( metric-space-ℝ l)
                  ( isometry-raise-real-ℚ l)
                  ( δ +ℚ⁺ δ +ℚ⁺ d)
                  ( p)
                  ( q)
                  ( Nxy (δ , δ , p , q) xp yq))
                ( is-in-neighborhood-real-is-in-cauchy-filter-ℚ
                  ( x)
                  ( δ)
                  ( p)
                  ( xp)))

          interchange-δd :
            (δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d) +ℚ⁺ δ) ＝ (d +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ)))
          interchange-δd =
            commutative-add-ℚ⁺ (δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d)) δ ∙
            inv (associative-add-ℚ⁺ δ δ (δ +ℚ⁺ δ +ℚ⁺ d)) ∙
            commutative-add-ℚ⁺ (δ +ℚ⁺ δ) (δ +ℚ⁺ δ +ℚ⁺ d) ∙
            ap (λ z → add-ℚ⁺ z (δ +ℚ⁺ δ)) (commutative-add-ℚ⁺ (δ +ℚ⁺ δ) d) ∙
            associative-add-ℚ⁺ d (δ +ℚ⁺ δ) (δ +ℚ⁺ δ)

          le-δμ : le-ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ)) μ
          le-δμ =
            transitive-le-ℚ⁺
              ( δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ))
              ( ε +ℚ⁺ ε)
              ( μ)
              ( ε+ε<μ)
              ( preserves-le-add-ℚ⁺
                { δ +ℚ⁺ δ}
                { ε}
                { δ +ℚ⁺ δ}
                { ε}
                ( δ+δ<ε)
                ( δ+δ<ε))

        monotonic-neighborhood-ℝ
          ( real-cauchy-filter-ℚ x)
          ( real-cauchy-filter-ℚ y)
          ( δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d) +ℚ⁺ δ)
          ( d +ℚ⁺ μ)
          ( inv-tr
            ( λ z → le-ℚ⁺ z (d +ℚ⁺ μ))
            ( interchange-δd)
            ( preserves-le-right-add-ℚ⁺ d (δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ)) μ le-δμ))
          ( N-real-xy)
```

### The map real-cauchy-filter-ℚ is short

```agda
module _
  {l : Level}
  where abstract

  is-expansive-map-real-cauchy-filter-ℚ :
    is-expansive-map-Metric-Space
      ( metric-space-cauchy-filter-ℚ l)
      ( metric-space-ℝ l)
      ( real-cauchy-filter-ℚ)
  is-expansive-map-real-cauchy-filter-ℚ d x y Nxy (α , β , p , q) xp yq =
    reflects-neighborhoods-map-isometry-Metric-Space
      ( metric-space-ℚ)
      ( metric-space-ℝ l)
      ( isometry-raise-real-ℚ l)
      ( α +ℚ⁺ β +ℚ⁺ d)
      ( p)
      ( q)
      ( inv-tr
        ( λ ε → neighborhood-ℝ l ε (raise-real-ℚ l p) (raise-real-ℚ l q))
        ( associative-add-ℚ⁺ α β d ∙ ap (add-ℚ⁺ α) (commutative-add-ℚ⁺ β d))
        ( Npq))
      where
        Npq :
          neighborhood-ℝ
            ( l)
            ( α +ℚ⁺ (d +ℚ⁺ β))
            ( raise-real-ℚ l p)
            ( raise-real-ℚ l q)
        Npq =
          is-triangular-neighborhood-ℝ
            ( raise-real-ℚ l p)
            ( real-cauchy-filter-ℚ x)
            ( raise-real-ℚ l q)
            ( α)
            ( d +ℚ⁺ β)
            ( is-triangular-neighborhood-ℝ
              ( real-cauchy-filter-ℚ x)
              ( real-cauchy-filter-ℚ y)
              ( raise-real-ℚ l q)
              ( d)
              ( β)
              ( is-in-neighborhood-real-is-in-cauchy-filter-ℚ y β q yq)
              ( Nxy))
            ( is-symmetric-neighborhood-ℝ
              ( α)
              ( real-cauchy-filter-ℚ x)
              ( raise-real-ℚ l p)
              ( is-in-neighborhood-real-is-in-cauchy-filter-ℚ x α p xp))
```

### The map real-cauchy-filter-ℚ is an isometry

```agda
module _
  {l : Level}
  where

  abstract
    is-isometry-real-cauchy-filter-ℚ :
      is-isometry-Metric-Space
        ( metric-space-cauchy-filter-ℚ l)
        ( metric-space-ℝ l)
        ( real-cauchy-filter-ℚ)
    is-isometry-real-cauchy-filter-ℚ =
      is-isometry-is-expansive-map-is-short-map-Metric-Space
        ( metric-space-cauchy-filter-ℚ l)
        ( metric-space-ℝ l)
        ( real-cauchy-filter-ℚ)
        ( is-short-map-real-cauchy-filter-ℚ)
        ( is-expansive-map-real-cauchy-filter-ℚ)

  isometry-real-cauchy-filter-ℚ :
    isometry-Metric-Space
      ( metric-space-cauchy-filter-ℚ l)
      ( metric-space-ℝ l)
  isometry-real-cauchy-filter-ℚ =
    ( real-cauchy-filter-ℚ , is-isometry-real-cauchy-filter-ℚ)
```

### The map cauchy-filter-ℚ-ℝ is an isometry

```agda
module _
  {l : Level}
  where abstract

  is-short-map-cauchy-filter-ℚ-ℝ :
    is-short-map-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-cauchy-filter-ℚ l)
      ( cauchy-filter-ℚ-ℝ)
  is-short-map-cauchy-filter-ℚ-ℝ d x y Nxy (α , β , u , v) Rxu Ryv =
    reflects-neighborhoods-map-isometry-Metric-Space
      ( metric-space-ℚ)
      ( metric-space-ℝ l)
      ( isometry-raise-real-ℚ l)
      ( α +ℚ⁺ β +ℚ⁺ d)
      ( u)
      ( v)
      ( inv-tr
        ( λ ε → neighborhood-ℝ l ε (raise-real-ℚ l u) (raise-real-ℚ l v))
        ( associative-add-ℚ⁺ α β d ∙ ap (add-ℚ⁺ α) (commutative-add-ℚ⁺ β d))
        ( Nuv))
    where

    Nuv :
      neighborhood-ℝ l (α +ℚ⁺ (d +ℚ⁺ β)) (raise-real-ℚ l u) (raise-real-ℚ l v)
    Nuv =
      is-triangular-neighborhood-ℝ
        ( raise-real-ℚ l u)
        ( x)
        ( raise-real-ℚ l v)
        ( α)
        ( d +ℚ⁺ β)
        ( is-triangular-neighborhood-ℝ
          ( x)
          ( y)
          ( raise-real-ℚ l v)
          ( d)
          ( β)
          ( Ryv)
          ( Nxy))
        ( is-symmetric-neighborhood-ℝ α x (raise-real-ℚ l u) Rxu)

  is-expansive-map-cauchy-filter-ℚ-ℝ :
    is-expansive-map-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-cauchy-filter-ℚ l)
      ( cauchy-filter-ℚ-ℝ)
  is-expansive-map-cauchy-filter-ℚ-ℝ d x y N-filter-xy =
    is-saturated-neighborhood-ℝ d x y saturate-Nxy
    where

    saturate-Nxy :
      (μ : ℚ⁺) → neighborhood-ℝ l (d +ℚ⁺ μ) x y
    saturate-Nxy μ =
      let
        open
          do-syntax-trunc-Prop
            ( neighborhood-prop-ℝ l (d +ℚ⁺ μ) x y)
      in do
        (ε , ε+ε<μ) ← double-le-ℚ⁺ μ
        (δ , δ+δ<ε) ← double-le-ℚ⁺ ε
        (p , Nxp) ← exists-rational-approximate-ℝ x δ
        (q , Nyq) ← exists-rational-approximate-ℝ y δ

        let
          Nxy : neighborhood-ℝ l (δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d) +ℚ⁺ δ) x y
          Nxy =
            is-triangular-neighborhood-ℝ
              ( x)
              ( raise-real-ℚ l q)
              ( y)
              ( δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d))
              ( δ)
              ( is-symmetric-neighborhood-ℝ δ y (raise-real-ℚ l q) Nyq)
              ( is-triangular-neighborhood-ℝ
                ( x)
                ( raise-real-ℚ l p)
                ( raise-real-ℚ l q)
                ( δ)
                ( δ +ℚ⁺ δ +ℚ⁺ d)
                ( preserves-neighborhoods-map-isometry-Metric-Space
                  ( metric-space-ℚ)
                  ( metric-space-ℝ l)
                  ( isometry-raise-real-ℚ l)
                  ( δ +ℚ⁺ δ +ℚ⁺ d)
                  ( p)
                  ( q)
                  ( N-filter-xy (δ , δ , p , q) Nxp Nyq))
                ( Nxp))

          interchange-δd :
            (δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d) +ℚ⁺ δ) ＝ (d +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ)))
          interchange-δd =
            commutative-add-ℚ⁺ (δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d)) δ ∙
            inv (associative-add-ℚ⁺ δ δ (δ +ℚ⁺ δ +ℚ⁺ d)) ∙
            commutative-add-ℚ⁺ (δ +ℚ⁺ δ) (δ +ℚ⁺ δ +ℚ⁺ d) ∙
            ap (λ z → add-ℚ⁺ z (δ +ℚ⁺ δ)) (commutative-add-ℚ⁺ (δ +ℚ⁺ δ) d) ∙
            associative-add-ℚ⁺ d (δ +ℚ⁺ δ) (δ +ℚ⁺ δ)

          le-δμ : le-ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ)) μ
          le-δμ =
            transitive-le-ℚ⁺
              ( δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ))
              ( ε +ℚ⁺ ε)
              ( μ)
              ( ε+ε<μ)
              ( preserves-le-add-ℚ⁺
                { δ +ℚ⁺ δ}
                { ε}
                { δ +ℚ⁺ δ}
                { ε}
                ( δ+δ<ε)
                ( δ+δ<ε))

        monotonic-neighborhood-ℝ
          ( x)
          ( y)
          ( δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d) +ℚ⁺ δ)
          ( d +ℚ⁺ μ)
          ( inv-tr
            ( λ z → le-ℚ⁺ z (d +ℚ⁺ μ))
            ( interchange-δd)
            ( preserves-le-right-add-ℚ⁺ d (δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ)) μ le-δμ))
          ( Nxy)

  is-isometry-cauchy-filter-ℚ-ℝ :
    is-isometry-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-cauchy-filter-ℚ l)
      ( cauchy-filter-ℚ-ℝ)
  is-isometry-cauchy-filter-ℚ-ℝ =
    is-isometry-is-expansive-map-is-short-map-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-cauchy-filter-ℚ l)
      ( cauchy-filter-ℚ-ℝ)
      ( is-short-map-cauchy-filter-ℚ-ℝ)
      ( is-expansive-map-cauchy-filter-ℚ-ℝ)
```

```agda
module _
  {l : Level}
  where

  isometry-cauchy-filter-ℚ-ℝ :
    isometry-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-cauchy-filter-ℚ l)
  isometry-cauchy-filter-ℚ-ℝ =
    ( cauchy-filter-ℚ-ℝ , is-isometry-cauchy-filter-ℚ-ℝ)
```

### Inverse laws

```agda
module _
  {l : Level} (x : ℝ l)
  where abstract

  opaque
    unfolding leq-ℝ

    is-upper-section-real-cauchy-filter-ℚ :
      leq-ℝ x (real-cauchy-filter-ℚ (cauchy-filter-ℚ-ℝ x))
    is-upper-section-real-cauchy-filter-ℚ p p<x =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ( ℚ⁺ × ℚ)
                ( λ (ε , q) →
                  ( le-ℚ-Prop (p +ℚ rational-ℚ⁺ ε) q) ∧
                  ( neighborhood-prop-ℝ l ε x (raise-real-ℚ l q))))
      in do
        ( r , p<r , r<x) ←
          forward-implication
            ( is-rounded-lower-cut-ℝ x p)
            ( p<x)

        let
          ε : ℚ⁺
          ε = positive-diff-le-ℚ p<r

        (q , x<q , Nxq) ← exists-rational-approximate-above-ℝ x ε

        let
          le-pε-q : le-ℚ (p +ℚ rational-ℚ⁺ ε) q
          le-pε-q =
            inv-tr
              ( λ z → le-ℚ z q)
              ( right-law-positive-diff-le-ℚ p<r)
              ( le-lower-upper-cut-ℝ x r<x x<q)

        intro-exists (ε , q) (le-pε-q , Nxq)

  opaque
    unfolding leq-ℝ'

    is-lower-section-real-cauchy-filter-ℚ :
      leq-ℝ' (real-cauchy-filter-ℚ (cauchy-filter-ℚ-ℝ x)) x
    is-lower-section-real-cauchy-filter-ℚ q x<q =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ( ℚ⁺ × ℚ)
                ( λ (ε , p) →
                  ( le-ℚ-Prop (p +ℚ rational-ℚ⁺ ε) q) ∧
                  ( neighborhood-prop-ℝ l ε x (raise-real-ℚ l p))))
      in do
        ( r , r<q , x<r) ←
          forward-implication
            ( is-rounded-upper-cut-ℝ x q)
            ( x<q)
        let
          ε : ℚ⁺
          ε = positive-diff-le-ℚ r<q

        (p , p<x , Nxp) ← exists-rational-approximate-below-ℝ x ε

        let
          le-pε-q : le-ℚ (p +ℚ rational-ℚ⁺ ε) q
          le-pε-q =
            tr
              ( λ z → le-ℚ (p +ℚ rational-ℚ⁺ ε) z)
              ( right-law-positive-diff-le-ℚ r<q)
              ( preserves-le-left-add-ℚ
                ( rational-ℚ⁺ ε)
                ( p)
                ( r)
                ( le-lower-upper-cut-ℝ x p<x x<r))

        intro-exists (ε , p) (le-pε-q , Nxp)

  is-section-real-cauchy-filter-ℚ :
    real-cauchy-filter-ℚ (cauchy-filter-ℚ-ℝ x) ＝ x
  is-section-real-cauchy-filter-ℚ =
    antisymmetric-leq-ℝ
      ( real-cauchy-filter-ℚ (cauchy-filter-ℚ-ℝ x))
      ( x)
      ( leq-leq'-ℝ
        ( real-cauchy-filter-ℚ (cauchy-filter-ℚ-ℝ x))
        ( x)
        ( is-lower-section-real-cauchy-filter-ℚ))
      ( is-upper-section-real-cauchy-filter-ℚ)
```

### The isometric equivalence between real numbers and Cauchy filters on the rational numbers

```agda
module _
  {l : Level}
  where

  equiv-real-cauchy-filter-ℚ : cauchy-filter-ℚ l ≃ ℝ l
  equiv-real-cauchy-filter-ℚ =
    ( real-cauchy-filter-ℚ ,
      is-equiv-is-section-isometry-Metric-Space
        ( metric-space-cauchy-filter-ℚ l)
        ( metric-space-ℝ l)
        ( isometry-real-cauchy-filter-ℚ)
        ( isometry-cauchy-filter-ℚ-ℝ)
        ( is-section-real-cauchy-filter-ℚ))

  isometric-equiv-real-cauchy-filter-ℚ :
    isometric-equiv-Metric-Space
      ( metric-space-cauchy-filter-ℚ l)
      ( metric-space-ℝ l)
  isometric-equiv-real-cauchy-filter-ℚ =
    ( equiv-real-cauchy-filter-ℚ , is-isometry-real-cauchy-filter-ℚ)

  eq-metric-space-real-cauchy-filter-ℚ :
    metric-space-cauchy-filter-ℚ l ＝ metric-space-ℝ l
  eq-metric-space-real-cauchy-filter-ℚ =
    eq-isometric-equiv-Metric-Space
      ( metric-space-cauchy-filter-ℚ l)
      ( metric-space-ℝ l)
      ( isometric-equiv-real-cauchy-filter-ℚ)

  eq-complete-metric-space-real-cauchy-filter-ℚ :
    complete-metric-space-cauchy-filter-ℚ l ＝ complete-metric-space-ℝ l
  eq-complete-metric-space-real-cauchy-filter-ℚ =
    eq-type-subtype
      ( is-complete-prop-Metric-Space)
      ( eq-metric-space-real-cauchy-filter-ℚ)
```
