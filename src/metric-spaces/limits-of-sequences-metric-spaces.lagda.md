# Limits of sequences in metric spaces

```agda
module metric-spaces.limits-of-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.metric-spaces
open import metric-spaces.modulated-uniformly-continuous-functions-metric-spaces
open import metric-spaces.sequences-metric-spaces
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces
```

</details>

## Ideas

An element `l` of a [metric space](metric-spaces.metric-spaces.md) is the
{{#concept "limit" Disambiguation="of a sequence in a metric spaces" WD="limit of a sequence" WDID=Q847204 Agda=is-limit-sequence-Metric-Space}}
of a [sequence in metric spaces](metric-spaces.sequences-metric-spaces.md) `u`
if there exists a function `m : ℚ⁺ → ℕ` such that whenever `m ε ≤ n` in `ℕ`,
`u n` is in an
[`ε`-neighborhood](metric-spaces.rational-neighborhood-relations.md) of `l`.

## Definition

### Limits of sequences in a metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u : sequence-type-Metric-Space M)
  (lim : type-Metric-Space M)
  where

  is-limit-modulus-prop-sequence-Metric-Space : (ℚ⁺ → ℕ) → Prop l2
  is-limit-modulus-prop-sequence-Metric-Space m =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( ℕ)
          ( λ ( n : ℕ) →
            hom-Prop
              ( leq-ℕ-Prop (m ε) n)
              ( neighborhood-prop-Metric-Space M ε (u n) lim)))

  is-limit-modulus-sequence-Metric-Space : (ℚ⁺ → ℕ) → UU l2
  is-limit-modulus-sequence-Metric-Space m =
    type-Prop (is-limit-modulus-prop-sequence-Metric-Space m)

  limit-modulus-sequence-Metric-Space : UU l2
  limit-modulus-sequence-Metric-Space =
    type-subtype is-limit-modulus-prop-sequence-Metric-Space

  modulus-limit-modulus-sequence-Metric-Space :
    limit-modulus-sequence-Metric-Space → ℚ⁺ → ℕ
  modulus-limit-modulus-sequence-Metric-Space m = pr1 m

  is-modulus-limit-modulus-sequence-Metric-Space :
    (m : limit-modulus-sequence-Metric-Space) →
    is-limit-modulus-sequence-Metric-Space
      (modulus-limit-modulus-sequence-Metric-Space m)
  is-modulus-limit-modulus-sequence-Metric-Space m = pr2 m

  is-limit-prop-sequence-Metric-Space : Prop l2
  is-limit-prop-sequence-Metric-Space =
    is-inhabited-subtype-Prop is-limit-modulus-prop-sequence-Metric-Space

  is-limit-sequence-Metric-Space : UU l2
  is-limit-sequence-Metric-Space =
    type-Prop is-limit-prop-sequence-Metric-Space
```

## Properties

### The limit of a sequence in a metric space is unique

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u : sequence-type-Metric-Space M)
  (x y : type-Metric-Space M)
  (Lx : is-limit-sequence-Metric-Space M u x)
  (Ly : is-limit-sequence-Metric-Space M u y)
  where

  sim-limit-sequence-Metric-Space : sim-Metric-Space M x y
  sim-limit-sequence-Metric-Space =
    rec-trunc-Prop
      ( sim-prop-Metric-Space M x y)
      ( λ My →
        rec-trunc-Prop
          ( Π-Prop ℚ⁺ (λ d → neighborhood-prop-Metric-Space M d x y))
          ( λ Mx →
            lemma-sim-limit-modulus-sequence-Metric-Space Mx My)
          ( Lx))
      ( Ly)
    where

    lemma-add-limit-modulus-sequence-Metric-Space :
      (d₁ d₂ : ℚ⁺) →
      Σ ( ℕ)
        ( λ N →
          (n : ℕ) →
          leq-ℕ N n →
          neighborhood-Metric-Space M d₁ (u n) x) →
      Σ ( ℕ)
        ( λ N →
          (n : ℕ) →
          leq-ℕ N n →
          neighborhood-Metric-Space M d₂ (u n) y) →
      neighborhood-Metric-Space M (d₁ +ℚ⁺ d₂) x y
    lemma-add-limit-modulus-sequence-Metric-Space d₁ d₂ (Nx , Mx) (Ny , My) =
      triangular-neighborhood-Metric-Space M
        ( x)
        ( u (max-ℕ Nx Ny))
        ( y)
        ( d₁)
        ( d₂)
        ( My (max-ℕ Nx Ny) (right-leq-max-ℕ Nx Ny))
        ( symmetric-neighborhood-Metric-Space M d₁
          ( u (max-ℕ Nx Ny))
          ( x)
          ( Mx (max-ℕ Nx Ny) (left-leq-max-ℕ Nx Ny)))

    lemma-sim-limit-modulus-sequence-Metric-Space :
      limit-modulus-sequence-Metric-Space M u x →
      limit-modulus-sequence-Metric-Space M u y →
      sim-Metric-Space M x y
    lemma-sim-limit-modulus-sequence-Metric-Space mx my ε =
      let
        (δ , η , δ+η=ε) = split-ℚ⁺ ε
        Nδ = modulus-limit-modulus-sequence-Metric-Space M u x mx δ
        Nη = modulus-limit-modulus-sequence-Metric-Space M u y my η
        Nε = max-ℕ Nδ Nη
        Nδ≤Nε = left-leq-max-ℕ Nδ Nη
        Nη≤Nε = right-leq-max-ℕ Nδ Nη

        δ-neighborhood : neighborhood-Metric-Space M δ (u Nε) x
        δ-neighborhood =
          is-modulus-limit-modulus-sequence-Metric-Space M u x mx δ Nε Nδ≤Nε

        η-neighborhood : neighborhood-Metric-Space M η (u Nε) y
        η-neighborhood =
          is-modulus-limit-modulus-sequence-Metric-Space M u y my η Nε Nη≤Nε

      in
        tr
          ( is-upper-bound-dist-Metric-Space M x y)
          ( δ+η=ε)
          ( triangular-neighborhood-Metric-Space
            ( M)
            ( x)
            ( u Nε)
            ( y)
            ( δ)
            ( η)
            ( η-neighborhood)
            ( symmetric-neighborhood-Metric-Space
              ( M)
              ( δ)
              ( u Nε)
              ( x)
              ( δ-neighborhood)))

  eq-limit-sequence-Metric-Space : x ＝ y
  eq-limit-sequence-Metric-Space =
    eq-sim-Metric-Space M x y sim-limit-sequence-Metric-Space
```

### Having a limit in a metric space is a proposition

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u : sequence-type-Metric-Space M)
  where

  has-limit-sequence-Metric-Space : UU (l1 ⊔ l2)
  has-limit-sequence-Metric-Space =
    Σ (type-Metric-Space M) (is-limit-sequence-Metric-Space M u)

  limit-has-limit-sequence-Metric-Space :
    has-limit-sequence-Metric-Space → type-Metric-Space M
  limit-has-limit-sequence-Metric-Space H = pr1 H

  is-limit-limit-has-limit-sequence-Metric-Space :
    (H : has-limit-sequence-Metric-Space) →
    is-limit-sequence-Metric-Space M u
      (limit-has-limit-sequence-Metric-Space H)
  is-limit-limit-has-limit-sequence-Metric-Space H = pr2 H

  is-prop-has-limit-sequence-Metric-Space :
    is-prop has-limit-sequence-Metric-Space
  is-prop-has-limit-sequence-Metric-Space =
    is-prop-all-elements-equal
      ( λ x y →
        eq-type-subtype
          ( is-limit-prop-sequence-Metric-Space M u)
          ( eq-limit-sequence-Metric-Space M u
            ( limit-has-limit-sequence-Metric-Space x)
            ( limit-has-limit-sequence-Metric-Space y)
            ( is-limit-limit-has-limit-sequence-Metric-Space x)
            ( is-limit-limit-has-limit-sequence-Metric-Space y)))

  has-limit-prop-sequence-Metric-Space : Prop (l1 ⊔ l2)
  has-limit-prop-sequence-Metric-Space =
    has-limit-sequence-Metric-Space ,
    is-prop-has-limit-sequence-Metric-Space
```

### Modulated uniformly continuous maps between metric spaces preserve limits

```agda
module _
  {la la' lb lb' : Level}
  (A : Metric-Space la la')
  (B : Metric-Space lb lb')
  (f : modulated-ucont-map-Metric-Space A B)
  (u : sequence-type-Metric-Space A)
  (lim : type-Metric-Space A)
  where

  abstract
    modulated-ucont-map-limit-modulus-sequence-Metric-Space :
      limit-modulus-sequence-Metric-Space A u lim →
      limit-modulus-sequence-Metric-Space
        ( B)
        ( map-sequence
          ( map-modulated-ucont-map-Metric-Space A B f)
          ( u))
        ( map-modulated-ucont-map-Metric-Space A B f lim)
    modulated-ucont-map-limit-modulus-sequence-Metric-Space (m , is-mod-m) =
      ( m ∘ modulus-modulated-ucont-map-Metric-Space A B f ,
        λ ε n N≤n →
          is-modulus-of-uniform-continuity-modulus-modulated-ucont-map-Metric-Space
            ( A)
            ( B)
            ( f)
            ( u n)
            ( ε)
            ( lim)
            ( is-mod-m
              ( modulus-modulated-ucont-map-Metric-Space A B f ε)
              ( n)
              ( N≤n)))

    modulated-ucont-map-limit-sequence-Metric-Space :
      is-limit-sequence-Metric-Space A u lim →
      is-limit-sequence-Metric-Space
        ( B)
        ( map-sequence
          ( map-modulated-ucont-map-Metric-Space A B f)
          ( u))
        ( map-modulated-ucont-map-Metric-Space A B f lim)
    modulated-ucont-map-limit-sequence-Metric-Space =
      map-is-inhabited modulated-ucont-map-limit-modulus-sequence-Metric-Space
```

### Uniformly continuous maps between metric spaces preserve limits

```agda
module _
  {la la' lb lb' : Level}
  (A : Metric-Space la la')
  (B : Metric-Space lb lb')
  (f : uniformly-continuous-function-Metric-Space A B)
  (u : sequence-type-Metric-Space A)
  (lim : type-Metric-Space A)
  where

  abstract
    uniformly-continuous-map-limit-sequence-Metric-Space :
      is-limit-sequence-Metric-Space A u lim →
      is-limit-sequence-Metric-Space
        ( B)
        ( map-sequence
          ( map-uniformly-continuous-function-Metric-Space A B f)
          ( u))
        ( map-uniformly-continuous-function-Metric-Space A B f lim)
    uniformly-continuous-map-limit-sequence-Metric-Space is-limit-lim =
      rec-trunc-Prop
        ( is-limit-prop-sequence-Metric-Space B _ _)
        ( λ m →
          modulated-ucont-map-limit-sequence-Metric-Space
            ( A)
            ( B)
            ( map-uniformly-continuous-function-Metric-Space A B f , m)
            ( u)
            ( lim)
            ( is-limit-lim))
        ( is-uniformly-continuous-map-uniformly-continuous-function-Metric-Space
          ( A)
          ( B)
          ( f))
```

### Short maps between metric spaces preserve limits

```agda
module _
  {la la' lb lb' : Level}
  (A : Metric-Space la la')
  (B : Metric-Space lb lb')
  (f : short-function-Metric-Space A B)
  (u : sequence-type-Metric-Space A)
  (lim : type-Metric-Space A)
  where

  short-map-limit-modulus-sequence-Metric-Space :
    limit-modulus-sequence-Metric-Space A u lim →
    limit-modulus-sequence-Metric-Space
      ( B)
      ( map-sequence
        ( map-short-function-Metric-Space A B f)
        ( u))
      ( map-short-function-Metric-Space A B f lim)
  short-map-limit-modulus-sequence-Metric-Space =
    modulated-ucont-map-limit-modulus-sequence-Metric-Space
      ( A)
      ( B)
      ( modulated-ucont-map-short-function-Metric-Space A B f)
      ( u)
      ( lim)

  short-map-limit-sequence-Metric-Space :
    is-limit-sequence-Metric-Space A u lim →
    is-limit-sequence-Metric-Space
      ( B)
      ( map-sequence
        ( map-short-function-Metric-Space A B f)
        ( u))
      ( map-short-function-Metric-Space A B f lim)
  short-map-limit-sequence-Metric-Space =
    map-is-inhabited short-map-limit-modulus-sequence-Metric-Space
```

## See also

- [Convergent sequences](metric-spaces.convergent-sequences-metric-spaces.md)
  are sequences with a limit;
- The
  [metric space of convergent sequences](metric-spaces.metric-space-of-convergent-sequences-metric-spaces.md)
  is the metric space of convergent sequences in a metric space with the product
  metric structure.

## External links

- [Limit of a sequence](https://en.wikipedia.org/wiki/Limit_of_a_sequence) at
  Wikipedia
