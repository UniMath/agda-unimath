# The uniform limit theorem for uniformly continuous maps between metric spaces

```agda
module metric-spaces.uniform-limit-theorem-uniformly-continuous-maps-metric-spaces where
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
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-space-of-maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.modulated-uniformly-continuous-maps-metric-spaces
open import metric-spaces.sequences-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces
```

</details>

## Idea

The
{{#concept "uniform limit theorem" WDID=Q7885107 WD="uniform limit theorem" Disambiguation="uniformly continuous maps between metric spaces" Agda=is-uniformly-continuous-map-is-uniform-limit-sequence-map-Metric-Space Agda=is-uniformly-continuous-map-is-uniform-limit-sequence-map-ACℕ-Metric-Space}}
states that uniform convergence of a sequence of
[maps between metric spaces](metric-spaces.maps-metric-spaces.md), i.e.,
convergence in the
[metric space of maps](metric-spaces.metric-space-of-maps-metric-spaces.md),
preserves
[uniform continuity](metric-spaces.uniformly-continuous-maps-metric-spaces.md).
If one has explicit moduli of uniform continuity for the maps, one can build a
modulus for the limit. Assuming the
[axiom of countable choice](foundation.axiom-of-countable-choice.md), the result
also applies to merely uniformly continuous maps.

## Theorem

### Uniform limits with a modulus of uniform convergence yield a modulus of uniform continuity

**Proof.** Let $u$ be a sequence of maps $uₙ : X → Y$ equipped with moduli of
uniform continuity $μₙ$, together with a modulus of uniform convergence $m$
towards $f$. Given $ε : ℚ⁺$, write $ε = (ε₁ + ε₂) + ε₃$, and let
$ε₁₃ = min(ε₁ , ε₃)$ and $N = m(ε₁₃)$. Uniform convergence gives $u_N(z)$ within
$ε₁₃$ of $f(z)$ for all $z : X$. Now set $δ = μ_N(ε₂)$. If $x'$ is within $δ$ of
$x$, then $u_N(x')$ is within $ε₂$ of $u_N(x)$. Combining this with the two
uniform bounds and applying the triangle inequality twice yields $f(x')$ within
$ε$ of $f(x)$. Thus we have constructed a modulus of uniform continuity for $f$.
∎

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (u : sequence (map-Metric-Space X Y))
  (f : map-Metric-Space X Y)
  where

  modulus-of-uniform-continuity-map-limit-modulus-sequence-map-Metric-Space :
    limit-modulus-sequence-Metric-Space
      ( metric-space-of-maps-Metric-Space X Y)
      ( u)
      ( f) →
    ( (n : ℕ) → modulus-of-uniform-continuity-map-Metric-Space X Y (u n)) →
    modulus-of-uniform-continuity-map-Metric-Space X Y f
  modulus-of-uniform-continuity-map-limit-modulus-sequence-map-Metric-Space
    L H =
    let
      m =
        modulus-limit-modulus-sequence-Metric-Space
          ( metric-space-of-maps-Metric-Space X Y)
          ( u)
          ( f)
          ( L)

      ε₁ = left-summand-split-ternary-ℚ⁺
      ε₂ = middle-summand-split-ternary-ℚ⁺
      ε₃ = right-summand-split-ternary-ℚ⁺
      ε₁₃ ε = min-ℚ⁺ (ε₁ ε) (ε₃ ε)

      N : ℚ⁺ → ℕ
      N ε = m (ε₁₃ ε)

      μN : (ε : ℚ⁺) → ℚ⁺ → ℚ⁺
      μN ε = pr1 (H (N ε))

      is-mod-μN :
        (ε : ℚ⁺) →
        is-modulus-of-uniform-continuity-map-Metric-Space
          X Y (u (N ε)) (μN ε)
      is-mod-μN ε = pr2 (H (N ε))

      uniform-min :
        (ε : ℚ⁺) (x : type-Metric-Space X) →
        neighborhood-Metric-Space Y (ε₁₃ ε) (u (N ε) x) (f x)
      uniform-min ε =
        is-modulus-limit-modulus-sequence-Metric-Space
          ( metric-space-of-maps-Metric-Space X Y)
          ( u)
          ( f)
          ( L)
          ( ε₁₃ ε)
          ( N ε)
          ( refl-leq-ℕ (N ε))

      uniform-left :
        (ε : ℚ⁺) (x : type-Metric-Space X) →
        neighborhood-Metric-Space Y (ε₁ ε) (u (N ε) x) (f x)
      uniform-left ε x =
        weakly-monotonic-neighborhood-Metric-Space
          ( Y)
          ( u (N ε) x)
          ( f x)
          ( ε₁₃ ε)
          ( ε₁ ε)
          ( leq-left-min-ℚ⁺ (ε₁ ε) (ε₃ ε))
          ( uniform-min ε x)

      uniform-right :
        (ε : ℚ⁺) (x : type-Metric-Space X) →
        neighborhood-Metric-Space Y (ε₃ ε) (u (N ε) x) (f x)
      uniform-right ε x =
        weakly-monotonic-neighborhood-Metric-Space
          ( Y)
          ( u (N ε) x)
          ( f x)
          ( ε₁₃ ε)
          ( ε₃ ε)
          ( leq-right-min-ℚ⁺ (ε₁ ε) (ε₃ ε))
          ( uniform-min ε x)

      modulus-f : ℚ⁺ → ℚ⁺
      modulus-f ε = μN ε (ε₂ ε)

      is-modulus-f :
        is-modulus-of-uniform-continuity-map-Metric-Space X Y f modulus-f
      is-modulus-f x ε x' Nx' =
        tr
          ( is-upper-bound-dist-Metric-Space Y (f x) (f x'))
          ( eq-add-split-ternary-ℚ⁺ ε)
          ( triangular-neighborhood-Metric-Space
            ( Y)
            ( f x)
            ( u (N ε) x')
            ( f x')
            ( ε₁ ε +ℚ⁺ ε₂ ε)
            ( ε₃ ε)
            ( uniform-right ε x')
            ( triangular-neighborhood-Metric-Space
              ( Y)
              ( f x)
              ( u (N ε) x)
              ( u (N ε) x')
              ( ε₁ ε)
              ( ε₂ ε)
              ( is-mod-μN ε x (ε₂ ε) x' Nx')
              ( symmetric-neighborhood-Metric-Space
                ( Y)
                ( ε₁ ε)
                ( u (N ε) x)
                ( f x)
                ( uniform-left ε x))))
    in
    ( modulus-f , is-modulus-f)
```

### Uniform limits of maps with a modulus of uniform continuity are uniformly continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (u : sequence (map-Metric-Space X Y))
  (f : map-Metric-Space X Y)
  where

  abstract
    is-uniformly-continuous-map-is-uniform-limit-sequence-map-Metric-Space :
      is-limit-sequence-Metric-Space
        ( metric-space-of-maps-Metric-Space X Y)
        ( u)
        ( f) →
      ( (n : ℕ) →
        modulus-of-uniform-continuity-map-Metric-Space X Y (u n)) →
      is-uniformly-continuous-map-Metric-Space X Y f
    is-uniformly-continuous-map-is-uniform-limit-sequence-map-Metric-Space
      L H =
      map-trunc-Prop
        ( λ L' →
          modulus-of-uniform-continuity-map-limit-modulus-sequence-map-Metric-Space
          ( X)
          ( Y)
          ( u)
          ( f)
          ( L')
          ( H))
        ( L)
```

### Uniform limits of maps with a truncated choice of moduli are uniformly continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (u : sequence (map-Metric-Space X Y))
  (f : map-Metric-Space X Y)
  where

  abstract
    is-uniformly-continuous-map-is-uniform-limit-sequence-map-trunc-Metric-Space :
      is-limit-sequence-Metric-Space
        ( metric-space-of-maps-Metric-Space X Y)
        ( u)
        ( f) →
      ║ ( (n : ℕ) →
          modulus-of-uniform-continuity-map-Metric-Space X Y (u n)) ║₋₁ →
      is-uniformly-continuous-map-Metric-Space X Y f
    is-uniformly-continuous-map-is-uniform-limit-sequence-map-trunc-Metric-Space
      L =
      rec-trunc-Prop
        ( is-uniformly-continuous-prop-map-Metric-Space X Y f)
        ( is-uniformly-continuous-map-is-uniform-limit-sequence-map-Metric-Space
          ( X)
          ( Y)
          ( u)
          ( f)
          ( L))
```

### Uniform limits of uniformly continuous maps are uniformly continuous, assuming the axiom of countable choice

```agda
module _
  {l1 l2 l3 l4 : Level}
  (acℕ : level-ACℕ (l1 ⊔ l2 ⊔ l4))
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (u : sequence (map-Metric-Space X Y))
  (f : map-Metric-Space X Y)
  where

  abstract
    is-uniformly-continuous-map-is-uniform-limit-sequence-map-ACℕ-Metric-Space :
      is-limit-sequence-Metric-Space
        ( metric-space-of-maps-Metric-Space X Y)
        ( u)
        ( f) →
      ( (n : ℕ) → is-uniformly-continuous-map-Metric-Space X Y (u n)) →
      is-uniformly-continuous-map-Metric-Space X Y f
    is-uniformly-continuous-map-is-uniform-limit-sequence-map-ACℕ-Metric-Space
      L H =
      rec-trunc-Prop
        ( is-uniformly-continuous-prop-map-Metric-Space X Y f)
        ( is-uniformly-continuous-map-is-uniform-limit-sequence-map-Metric-Space
          ( X)
          ( Y)
          ( u)
          ( f)
          ( L))
        ( acℕ (modulus-of-uniform-continuity-set-map-Metric-Space X Y ∘ u) H)
```

## External links

- [Uniform limit theorem](https://en.wikipedia.org/wiki/Uniform_limit_theorem)
  on Wikipedia
