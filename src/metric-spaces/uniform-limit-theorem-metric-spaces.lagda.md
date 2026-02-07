# The uniform limit theorem in metric spaces

```agda
module metric-spaces.uniform-limit-theorem-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.axiom-of-countable-choice
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-space-of-maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pointwise-continuous-maps-metric-spaces
open import metric-spaces.pointwise-epsilon-delta-continuous-maps-metric-spaces
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

The
{{#concept "uniform limit theorem" WDID=Q7885107 WD="uniform limit theorem" Agda=is-pointwise-ε-δ-continuous-map-is-uniform-limit-sequence-map-Metric-Space}}
states that uniform convergence of a sequence of
[maps between metric spaces](metric-spaces.maps-metric-spaces.md), i.e.,
convergence in the
[metric space of maps](metric-spaces.metric-space-of-maps-metric-spaces.md),
preserves
[pointwise ε-δ continuity](metric-spaces.pointwise-epsilon-delta-continuous-maps-metric-spaces.md)
Assuming the
[axiom of countable choice](foundation.axiom-of-countable-choice.md), this also
yields
[pointwise continuity](metric-spaces.pointwise-continuous-maps-metric-spaces.md).

## Theorem

### Uniform limits of pointwise ε-δ continuous maps are pointwise ε-δ continuous

**Proof.** Let $u$ be a sequence of pointwise ε-δ continuous maps $uₙ : X → Y$
that uniformly converges to $f$, i.e., it converges in the metric space of maps.
Given arbitrary $x : X$ and $ε : ℚ⁺$, we must produce $δ : ℚ⁺$ such that every
$x' : X$ in the $δ$-neighborhood of $x$ is sent by $f$ into the $ε$-neighborhood
of $f(x)$.

Since $u$ converges uniformly to $f$, choose a modulus $m$ of convergence. Write
$ε$ as a ternary sum of positive rationals $ε = (ε₁ + ε₂) + ε₃$, and let
$ε₁₃ = min(ε₁ , ε₃)$ and $N = m(ε₁₃)$. By uniform convergence at stage $N$, for
every $z : X$, $u_N(z)$ lies in the $ε₁₃$-neighborhood of $f(z)$, hence in
particular in the $ε₁$-neighborhood and in the $ε₃$-neighborhood of $f(z)$.

Now use pointwise ε-δ continuity of $u_N$ at $x$ with error $ε₂$: there is
$δ : ℚ⁺$ such that every $x'$ in the $δ$-neighborhood of $x$ is mapped by $u_N$
to the $ε₂$-neighborhood of $u_N(x)$.

Take such an $x'$. By symmetry, $f(x)$ lies in the $ε₁$-neighborhood of
$u_N(x)$. Combining this with the previous two bounds and applying the triangle
inequality twice along $f(x) → u_N(x) → u_N(x') → f(x')$, we get that $f(x')$
lies in the $ε$-neighborhood of $f(x)$. Therefore $f$ is pointwise ε-δ
continuous at $x$. ∎

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (u : sequence (map-Metric-Space X Y))
  (f : map-Metric-Space X Y)
  where

  abstract
    is-pointwise-ε-δ-continuous-map-is-uniform-limit-sequence-map-Metric-Space :
      is-limit-sequence-Metric-Space
        ( metric-space-of-maps-Metric-Space X Y)
        ( u)
        ( f) →
      ( (n : ℕ) → is-pointwise-ε-δ-continuous-map-Metric-Space X Y (u n)) →
      is-pointwise-ε-δ-continuous-map-Metric-Space X Y f
    is-pointwise-ε-δ-continuous-map-is-uniform-limit-sequence-map-Metric-Space
      L H x ε =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ( ℚ⁺)
                ( λ δ →
                  Π-Prop
                    ( type-Metric-Space X)
                    ( λ x' →
                      neighborhood-prop-Metric-Space X δ x x' ⇒
                      neighborhood-prop-Metric-Space Y ε (f x) (f x'))))
      in do
        (m , is-mod-m) ← L
        let
          ε₁ = left-summand-split-ternary-ℚ⁺ ε
          ε₂ = middle-summand-split-ternary-ℚ⁺ ε
          ε₃ = right-summand-split-ternary-ℚ⁺ ε
          ε₁₃ = min-ℚ⁺ ε₁ ε₃
          N = m ε₁₃

          uniform-min :
            (x : type-Metric-Space X) →
            neighborhood-Metric-Space Y ε₁₃ (u N x) (f x)
          uniform-min =
            is-modulus-limit-modulus-sequence-Metric-Space
              ( metric-space-of-maps-Metric-Space X Y)
              ( u)
              ( f)
              ( m , is-mod-m)
              ( ε₁₃)
              ( N)
              ( refl-leq-ℕ N)

          uniform-left :
            (x : type-Metric-Space X) →
            neighborhood-Metric-Space Y ε₁ (u N x) (f x)
          uniform-left x =
            weakly-monotonic-neighborhood-Metric-Space
              ( Y)
              ( u N x)
              ( f x)
              ( ε₁₃)
              ( ε₁)
              ( leq-left-min-ℚ⁺ ε₁ ε₃)
              ( uniform-min x)

          uniform-right :
            (x : type-Metric-Space X) →
            neighborhood-Metric-Space Y ε₃ (u N x) (f x)
          uniform-right x =
            weakly-monotonic-neighborhood-Metric-Space
              ( Y)
              ( u N x)
              ( f x)
              ( ε₁₃)
              ( ε₃)
              ( leq-right-min-ℚ⁺ ε₁ ε₃)
              ( uniform-min x)

        (δ , is-mod-δ) ← H N x ε₂

        intro-exists
          ( δ)
          ( λ x' Nx' →
            tr
              ( is-upper-bound-dist-Metric-Space Y (f x) (f x'))
              ( eq-add-split-ternary-ℚ⁺ ε)
              ( triangular-neighborhood-Metric-Space
                ( Y)
                ( f x)
                ( u N x')
                ( f x')
                ( ε₁ +ℚ⁺ ε₂)
                ( ε₃)
                ( uniform-right x')
                ( triangular-neighborhood-Metric-Space
                  ( Y)
                  ( f x)
                  ( u N x)
                  ( u N x')
                  ( ε₁)
                  ( ε₂)
                  ( is-mod-δ x' Nx')
                  ( symmetric-neighborhood-Metric-Space
                    ( Y)
                    ( ε₁)
                    ( u N x)
                    ( f x)
                    ( uniform-left x)))))
```

### Uniform limits of pointwise continuous maps are pointwise ε-δ continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (u : sequence (map-Metric-Space X Y))
  (f : map-Metric-Space X Y)
  where

  abstract
    is-pointwise-ε-δ-continuous-map-is-uniform-limit-sequence-map-is-pointwise-continuous-map-Metric-Space :
      is-limit-sequence-Metric-Space
        ( metric-space-of-maps-Metric-Space X Y)
        ( u)
        ( f) →
      ( (n : ℕ) → is-pointwise-continuous-map-Metric-Space X Y (u n)) →
      is-pointwise-ε-δ-continuous-map-Metric-Space X Y f
    is-pointwise-ε-δ-continuous-map-is-uniform-limit-sequence-map-is-pointwise-continuous-map-Metric-Space
      L H =
      is-pointwise-ε-δ-continuous-map-is-uniform-limit-sequence-map-Metric-Space
        ( X)
        ( Y)
        ( u)
        ( f)
        ( L)
        ( λ n →
          is-pointwise-ε-δ-continuous-map-pointwise-continuous-map-Metric-Space
            ( X)
            ( Y)
            ( u n , H n))
```

### Uniform limits of pointwise continuous maps are pointwise continuous, assuming the axiom of countable choice

```agda
module _
  {l1 l2 l3 l4 : Level}
  (acω : level-ACℕ (l1 ⊔ l2 ⊔ l4))
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (u : sequence (map-Metric-Space X Y))
  (f : map-Metric-Space X Y)
  where

  abstract
    is-pointwise-continuous-map-is-uniform-limit-sequence-map-ACℕ-Metric-Space :
      is-limit-sequence-Metric-Space
        ( metric-space-of-maps-Metric-Space X Y)
        ( u)
        ( f) →
      ( (n : ℕ) → is-pointwise-continuous-map-Metric-Space X Y (u n)) →
      is-pointwise-continuous-map-Metric-Space X Y f
    is-pointwise-continuous-map-is-uniform-limit-sequence-map-ACℕ-Metric-Space
      L H =
      is-pointwise-continuous-is-pointwise-ε-δ-continuous-map-ACℕ-Metric-Space
        ( acω)
        ( X)
        ( Y)
        ( f)
        ( is-pointwise-ε-δ-continuous-map-is-uniform-limit-sequence-map-is-pointwise-continuous-map-Metric-Space
          ( X)
          ( Y)
          ( u)
          ( f)
          ( L)
          ( H))
```

## External links

- [Uniform limit theorem](https://en.wikipedia.org/wiki/Uniform_limit_theorem)
  on Wikipedia
