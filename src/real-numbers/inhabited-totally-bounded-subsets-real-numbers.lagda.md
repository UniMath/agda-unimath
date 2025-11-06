# Inhabited totally bounded subsets of the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.inhabited-totally-bounded-subsets-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.images
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.propositionally-decidable-types

open import metric-spaces.approximations-metric-spaces
open import metric-spaces.inhabited-totally-bounded-subspaces-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.nets-metric-spaces
open import metric-spaces.subspaces-metric-spaces
open import metric-spaces.totally-bounded-metric-spaces

open import order-theory.upper-bounds-large-posets

open import real-numbers.absolute-value-closed-intervals-real-numbers
open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.cauchy-completeness-dedekind-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.infima-and-suprema-families-real-numbers
open import real-numbers.infima-families-real-numbers
open import real-numbers.inhabited-finitely-enumerable-subsets-real-numbers
open import real-numbers.maximum-inhabited-finitely-enumerable-subsets-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.subsets-real-numbers
open import real-numbers.suprema-families-real-numbers
open import real-numbers.totally-bounded-subsets-real-numbers

open import univalent-combinatorics.inhabited-finitely-enumerable-subtypes
```

</details>

## Idea

A [subset of the real numbers](real-numbers.subsets-real-numbers.md) is
{{#concept "inhabited and totally bounded" Disambiguation="subset of the real numbers" Agda=inhabited-totally-bounded-subset-ℝ}}
if it is an
[inhabited, totally bounded subspace](metric-spaces.inhabited-totally-bounded-subspaces-metric-spaces.md)
of the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

```agda
inhabited-totally-bounded-subset-ℝ :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
inhabited-totally-bounded-subset-ℝ l1 l2 l3 =
  inhabited-totally-bounded-subspace-Metric-Space l1 l3 (metric-space-ℝ l2)

module _
  {l1 l2 l3 : Level} (S : inhabited-totally-bounded-subset-ℝ l1 l2 l3)
  where

  totally-bounded-subset-inhabited-totally-bounded-subset-ℝ :
    totally-bounded-subset-ℝ l1 l2 l3
  totally-bounded-subset-inhabited-totally-bounded-subset-ℝ =
    totally-bounded-subspace-inhabited-totally-bounded-subspace-Metric-Space
      ( metric-space-ℝ l2)
      ( S)

  subset-inhabited-totally-bounded-subset-ℝ : subset-ℝ l1 l2
  subset-inhabited-totally-bounded-subset-ℝ =
    subset-inhabited-totally-bounded-subspace-Metric-Space
      ( metric-space-ℝ l2)
      ( S)

  is-in-inhabited-totally-bounded-subset-ℝ : ℝ l2 → UU l1
  is-in-inhabited-totally-bounded-subset-ℝ =
    is-in-subtype subset-inhabited-totally-bounded-subset-ℝ

  type-inhabited-totally-bounded-subset-ℝ : UU (l1 ⊔ lsuc l2)
  type-inhabited-totally-bounded-subset-ℝ =
    type-subtype subset-inhabited-totally-bounded-subset-ℝ

  subspace-inhabited-totally-bounded-subset-ℝ :
    Metric-Space (l1 ⊔ lsuc l2) l2
  subspace-inhabited-totally-bounded-subset-ℝ =
    subspace-inhabited-totally-bounded-subspace-Metric-Space
      ( metric-space-ℝ l2)
      ( S)

  is-totally-bounded-subspace-inhabited-totally-bounded-subset-ℝ :
    is-totally-bounded-Metric-Space
      ( l3)
      ( subspace-inhabited-totally-bounded-subset-ℝ)
  is-totally-bounded-subspace-inhabited-totally-bounded-subset-ℝ =
    is-totally-bounded-subspace-inhabited-totally-bounded-subspace-Metric-Space
      ( metric-space-ℝ l2)
      ( S)

  is-inhabited-inhabited-totally-bounded-subset-ℝ :
    is-inhabited-subtype subset-inhabited-totally-bounded-subset-ℝ
  is-inhabited-inhabited-totally-bounded-subset-ℝ =
    is-inhabited-inhabited-totally-bounded-subspace-Metric-Space
      ( metric-space-ℝ l2)
      ( S)
```

## Properties

### The elementwise negation of an inhabited totally bounded subset of ℝ is inhabited and totally bounded

```agda
neg-inhabited-totally-bounded-subset-ℝ :
  {l1 l2 l3 : Level} →
  inhabited-totally-bounded-subset-ℝ l1 l2 l3 →
  inhabited-totally-bounded-subset-ℝ l1 l2 (l1 ⊔ lsuc l2 ⊔ l3)
neg-inhabited-totally-bounded-subset-ℝ (S@(S' , _) , |S|) =
  ( neg-totally-bounded-subset-ℝ S ,
    neg-is-inhabited-subset-ℝ S' |S|)
```

### Inhabited, totally bounded subsets of ℝ have a supremum

This proof is adapted from Theorem 11.5.7 of {{#cite UF13}}.

```agda
module _
  {l1 l2 l3 : Level} (S : subset-ℝ l1 l2) (|S| : is-inhabited-subtype S)
  (M : modulus-of-total-boundedness-subset-ℝ l3 S)
  where

  private
    net : ℚ⁺ → inhabited-finitely-enumerable-subset-ℝ (l1 ⊔ lsuc l2 ⊔ l3) l2
    net δ =
      im-inhabited-finitely-enumerable-subtype
        ( inclusion-subset-ℝ S)
        ( inhabited-finitely-enumerable-subset-net-is-inhabited-Metric-Space
          ( metric-space-subset-ℝ S)
          ( δ)
          ( M δ)
          ( |S|))

    is-net :
      (δ : ℚ⁺) →
      is-approximation-Metric-Space
        ( metric-space-subset-ℝ S)
        ( δ)
        ( subset-net-Metric-Space (metric-space-subset-ℝ S) δ (M δ))
    is-net δ = pr2 (M δ)

    net⊆S :
      (δ : ℚ⁺) → (subset-inhabited-finitely-enumerable-subset-ℝ (net δ)) ⊆ S
    net⊆S δ n =
      rec-trunc-Prop
        ( S n)
        ( λ z → tr (type-Prop ∘ S) (pr2 z) (pr2 (pr1 (pr1 z))))

    max-net : ℚ⁺ → ℝ l2
    max-net δ = max-inhabited-finitely-enumerable-subset-ℝ (net δ)

  abstract
    cauchy-approximation-sup-modulated-totally-bounded-subset-ℝ :
      cauchy-approximation-ℝ l2
    cauchy-approximation-sup-modulated-totally-bounded-subset-ℝ =
      let
        bound : (ε η : ℚ⁺) → leq-ℝ (max-net ε) (max-net η +ℝ real-ℚ⁺ η)
        bound ε η =
          forward-implication
            ( is-least-upper-bound-max-inhabited-finitely-enumerable-subset-ℝ
              ( net ε)
              ( max-net η +ℝ real-ℚ⁺ η))
            ( λ (z , z∈net-ε) →
              let
                open
                  do-syntax-trunc-Prop
                    ( leq-prop-ℝ z (max-net η +ℝ real-ℚ⁺ η))
              in do
                (((y , y∈S) , y∈net-η) , Nηyz) ←
                  is-net η (z , net⊆S ε z z∈net-ε)
                transitive-leq-ℝ
                  ( z)
                  ( y +ℝ real-ℚ⁺ η)
                  ( max-net η +ℝ real-ℚ⁺ η)
                  ( preserves-leq-right-add-ℝ
                    ( real-ℚ⁺ η)
                    ( y)
                    ( max-net η)
                    ( is-upper-bound-max-inhabited-finitely-enumerable-subset-ℝ
                      ( net η)
                      ( map-unit-im (pr1 ∘ pr1) (((y , y∈S) , y∈net-η)))))
                  ( right-leq-real-bound-neighborhood-ℝ η _ _ Nηyz))
      in
        ( max-net ,
          λ ε η →
            neighborhood-real-bound-each-leq-ℝ (ε +ℚ⁺ η) _ _
              ( transitive-leq-ℝ
                ( max-net ε)
                ( max-net η +ℝ real-ℚ⁺ η)
                ( max-net η +ℝ real-ℚ⁺ (ε +ℚ⁺ η))
                ( preserves-leq-left-add-ℝ (max-net η) _ _
                  ( preserves-leq-real-ℚ _ _ (leq-left-add-rational-ℚ⁺ _ ε)))
                ( bound ε η))
              ( transitive-leq-ℝ
                ( max-net η)
                ( max-net ε +ℝ real-ℚ⁺ ε)
                ( max-net ε +ℝ real-ℚ⁺ (ε +ℚ⁺ η))
                ( preserves-leq-left-add-ℝ (max-net ε) _ _
                  ( preserves-leq-real-ℚ _ _ (leq-right-add-rational-ℚ⁺ _ η)))
                ( bound η ε)))

    sup-modulated-totally-bounded-subset-ℝ : ℝ l2
    sup-modulated-totally-bounded-subset-ℝ =
      lim-cauchy-approximation-ℝ
        ( cauchy-approximation-sup-modulated-totally-bounded-subset-ℝ)

    is-upper-bound-sup-modulated-totally-bounded-subset-ℝ :
      is-upper-bound-family-of-elements-Large-Poset
        ( ℝ-Large-Poset)
        ( inclusion-subset-ℝ S)
        ( sup-modulated-totally-bounded-subset-ℝ)
    is-upper-bound-sup-modulated-totally-bounded-subset-ℝ (x , x∈S) =
      leq-not-le-ℝ _ _
        ( λ sup<x →
          let
            sup = sup-modulated-totally-bounded-subset-ℝ
            open do-syntax-trunc-Prop empty-Prop
          in do
            (ε , sup+ε<x) ← exists-positive-rational-separation-le-ℝ sup<x
            (ε' , ε'+ε'<ε) ← double-le-ℚ⁺ ε
            (((y , y∈S) , y∈net-ε') , Nε'yx) ← pr2 (M ε') (x , x∈S)
            irreflexive-le-ℝ x
              ( concatenate-leq-le-ℝ
                ( x)
                ( y +ℝ real-ℚ⁺ ε')
                ( x)
                ( right-leq-real-bound-neighborhood-ℝ ε' _ _ Nε'yx)
                ( transitive-le-ℝ
                  ( y +ℝ real-ℚ⁺ ε')
                  ( sup-modulated-totally-bounded-subset-ℝ +ℝ real-ℚ⁺ ε)
                  ( x)
                  ( sup+ε<x)
                  ( concatenate-leq-le-ℝ
                    ( y +ℝ real-ℚ⁺ ε')
                    ( sup +ℝ real-ℚ⁺ (ε' +ℚ⁺ ε'))
                    ( sup +ℝ real-ℚ⁺ ε)
                    ( tr
                      ( leq-ℝ (y +ℝ real-ℚ⁺ ε'))
                      ( associative-add-ℝ _ _ _ ∙
                        ap-add-ℝ refl (add-real-ℚ _ _))
                      ( preserves-leq-right-add-ℝ (real-ℚ⁺ ε') _ _
                        ( transitive-leq-ℝ _ _ _
                          ( left-leq-real-bound-neighborhood-ℝ ε' _ _
                            ( saturated-is-limit-lim-cauchy-approximation-ℝ
                              ( cauchy-approximation-sup-modulated-totally-bounded-subset-ℝ)
                              ( ε')))
                          ( is-upper-bound-max-inhabited-finitely-enumerable-subset-ℝ
                            ( net ε')
                            ( map-unit-im
                              ( pr1 ∘ pr1)
                              ( (y , y∈S) , y∈net-ε'))))))
                    ( preserves-le-left-add-ℝ sup _ _
                      ( preserves-le-real-ℚ _ _ ε'+ε'<ε))))))

    is-approximated-below-sup-modulated-totally-bounded-subset-ℝ :
      is-approximated-below-family-ℝ
        ( inclusion-subset-ℝ S)
        ( sup-modulated-totally-bounded-subset-ℝ)
    is-approximated-below-sup-modulated-totally-bounded-subset-ℝ ε =
      let
        sup = sup-modulated-totally-bounded-subset-ℝ
        open
          do-syntax-trunc-Prop
            ( ∃
              ( type-subtype S)
              ( λ (s , s∈S) →
                le-prop-ℝ
                  ( sup-modulated-totally-bounded-subset-ℝ -ℝ real-ℚ⁺ ε)
                  ( s)))
      in do
        (ε' , ε'+ε'<ε) ← double-le-ℚ⁺ ε
        ((x , x∈net-ε') , max-net-ε'-ε'<x) ←
          is-approximated-below-max-inhabited-finitely-enumerable-subset-ℝ
            ( net ε')
            ( ε')
        intro-exists
          ( x , net⊆S ε' x x∈net-ε')
          ( transitive-le-ℝ
            ( sup -ℝ real-ℚ⁺ ε)
            ( max-net ε' -ℝ real-ℚ⁺ ε')
            ( x)
            ( max-net-ε'-ε'<x)
            ( concatenate-le-leq-ℝ
              ( sup -ℝ real-ℚ⁺ ε)
              ( sup -ℝ real-ℚ⁺ (ε' +ℚ⁺ ε'))
              ( max-net ε' -ℝ real-ℚ⁺ ε')
              ( reverses-le-diff-ℝ sup _ _ (preserves-le-real-ℚ _ _ ε'+ε'<ε))
              ( tr
                ( λ y → leq-ℝ y (max-net ε' -ℝ real-ℚ⁺ ε'))
                ( associative-add-ℝ _ _ _ ∙
                  ap-add-ℝ refl (inv (distributive-neg-add-ℝ _ _)) ∙
                  ap-diff-ℝ refl (add-real-ℚ _ _))
                ( preserves-leq-diff-ℝ (real-ℚ⁺ ε') _ _
                  ( leq-transpose-right-add-ℝ _ _ _
                    ( right-leq-real-bound-neighborhood-ℝ ε' _ _
                      ( saturated-is-limit-lim-cauchy-approximation-ℝ
                        ( cauchy-approximation-sup-modulated-totally-bounded-subset-ℝ)
                        ( ε'))))))))

    is-supremum-sup-modulated-totally-bounded-subset-ℝ :
      is-supremum-subset-ℝ S sup-modulated-totally-bounded-subset-ℝ
    is-supremum-sup-modulated-totally-bounded-subset-ℝ =
      ( is-upper-bound-sup-modulated-totally-bounded-subset-ℝ ,
        is-approximated-below-sup-modulated-totally-bounded-subset-ℝ)

    has-supremum-modulated-totally-bounded-subset-ℝ : has-supremum-subset-ℝ S l2
    has-supremum-modulated-totally-bounded-subset-ℝ =
      ( sup-modulated-totally-bounded-subset-ℝ ,
        is-supremum-sup-modulated-totally-bounded-subset-ℝ)

module _
  {l1 l2 l3 : Level}
  (S : inhabited-totally-bounded-subset-ℝ l1 l2 l3)
  where

  abstract
    has-supremum-inhabited-totally-bounded-subset-ℝ :
      has-supremum-subset-ℝ (subset-inhabited-totally-bounded-subset-ℝ S) l2
    has-supremum-inhabited-totally-bounded-subset-ℝ =
      rec-trunc-Prop
        ( has-supremum-prop-subset-ℝ
          ( subset-inhabited-totally-bounded-subset-ℝ S)
          ( l2))
        ( has-supremum-modulated-totally-bounded-subset-ℝ
          ( subset-inhabited-totally-bounded-subset-ℝ S)
          ( is-inhabited-inhabited-totally-bounded-subset-ℝ S))
        ( is-totally-bounded-subspace-inhabited-totally-bounded-subset-ℝ S)

    sup-inhabited-totally-bounded-subset-ℝ : ℝ l2
    sup-inhabited-totally-bounded-subset-ℝ =
      pr1 has-supremum-inhabited-totally-bounded-subset-ℝ

    is-supremum-sup-inhabited-totally-bounded-subset-ℝ :
      is-supremum-subset-ℝ
        ( subset-inhabited-totally-bounded-subset-ℝ S)
        ( sup-inhabited-totally-bounded-subset-ℝ)
    is-supremum-sup-inhabited-totally-bounded-subset-ℝ =
      pr2 has-supremum-inhabited-totally-bounded-subset-ℝ
```

### Inhabited, totally bounded subsets of ℝ have an infimum

```agda
module _
  {l1 l2 l3 : Level}
  (S : inhabited-totally-bounded-subset-ℝ l1 l2 l3)
  where

  abstract
    inf-inhabited-totally-bounded-subset-ℝ : ℝ l2
    inf-inhabited-totally-bounded-subset-ℝ =
      neg-ℝ
        ( sup-inhabited-totally-bounded-subset-ℝ
          ( neg-inhabited-totally-bounded-subset-ℝ S))

    is-infimum-inf-inhabited-totally-bounded-subset-ℝ :
      is-infimum-subset-ℝ
        ( subset-inhabited-totally-bounded-subset-ℝ S)
        ( inf-inhabited-totally-bounded-subset-ℝ)
    is-infimum-inf-inhabited-totally-bounded-subset-ℝ =
      is-infimum-neg-supremum-neg-subset-ℝ
        ( subset-inhabited-totally-bounded-subset-ℝ S)
        ( sup-inhabited-totally-bounded-subset-ℝ
          ( neg-inhabited-totally-bounded-subset-ℝ S))
        ( is-supremum-sup-inhabited-totally-bounded-subset-ℝ
          ( neg-inhabited-totally-bounded-subset-ℝ S))

    has-infimum-inhabited-totally-bounded-subset-ℝ :
      has-infimum-subset-ℝ (subset-inhabited-totally-bounded-subset-ℝ S) l2
    has-infimum-inhabited-totally-bounded-subset-ℝ =
      ( inf-inhabited-totally-bounded-subset-ℝ ,
        is-infimum-inf-inhabited-totally-bounded-subset-ℝ)
```

### Any totally bounded subset of `ℝ` is propositionally decidable

```agda
module _
  {l1 l2 l3 : Level}
  (S : totally-bounded-subset-ℝ l1 l2 l3)
  where

  abstract
    is-inhabited-or-empty-totally-bounded-subset-ℝ :
      is-inhabited-or-empty (type-totally-bounded-subset-ℝ S)
    is-inhabited-or-empty-totally-bounded-subset-ℝ =
      is-inhabited-or-empty-totally-bounded-subspace-Metric-Space
        ( metric-space-ℝ l2)
        ( S)
```

### The infimum of an inhabited totally bounded subset of `ℝ` is less than or equal to the supremum

```agda
module _
  {l1 l2 l3 : Level}
  (S : inhabited-totally-bounded-subset-ℝ l1 l2 l3)
  where

  abstract
    leq-inf-sup-inhabited-totally-bounded-subset-ℝ :
      leq-ℝ
        ( inf-inhabited-totally-bounded-subset-ℝ S)
        ( sup-inhabited-totally-bounded-subset-ℝ S)
    leq-inf-sup-inhabited-totally-bounded-subset-ℝ =
      leq-inf-sup-subset-ℝ
        ( subset-inhabited-totally-bounded-subset-ℝ S)
        ( inf-inhabited-totally-bounded-subset-ℝ S)
        ( is-infimum-inf-inhabited-totally-bounded-subset-ℝ S)
        ( sup-inhabited-totally-bounded-subset-ℝ S)
        ( is-supremum-sup-inhabited-totally-bounded-subset-ℝ S)
```

### An inhabited totally bounded subset `S` of `ℝ` is a subset of the closed interval `[inf S , sup S]`

```agda
module _
  {l1 l2 l3 : Level}
  (S : inhabited-totally-bounded-subset-ℝ l1 l2 l3)
  where

  enclosing-closed-interval-inhabited-totally-bounded-subset-ℝ :
    closed-interval-ℝ l2 l2
  enclosing-closed-interval-inhabited-totally-bounded-subset-ℝ =
    ( ( inf-inhabited-totally-bounded-subset-ℝ S ,
        sup-inhabited-totally-bounded-subset-ℝ S) ,
      leq-inf-sup-inhabited-totally-bounded-subset-ℝ S)

  subset-enclosing-closed-interval-inhabited-totally-bounded-subset-ℝ :
    subset-inhabited-totally-bounded-subset-ℝ S ⊆
    subtype-closed-interval-ℝ
      ( l2)
      ( enclosing-closed-interval-inhabited-totally-bounded-subset-ℝ)
  subset-enclosing-closed-interval-inhabited-totally-bounded-subset-ℝ s s∈S =
    ( is-lower-bound-is-infimum-family-ℝ _ _
        ( is-infimum-inf-inhabited-totally-bounded-subset-ℝ S)
        ( s , s∈S) ,
      is-upper-bound-is-supremum-family-ℝ _ _
        ( is-supremum-sup-inhabited-totally-bounded-subset-ℝ S)
        ( s , s∈S))
```

### There is a nonnegative upper bound on the absolute value of an element of an inhabited totally bounded subset of `ℝ`

```agda
module _
  {l1 l2 l3 : Level}
  (S : inhabited-totally-bounded-subset-ℝ l1 l2 l3)
  where

  abstract
    nonnegative-upper-bound-abs-is-in-inhabited-totally-bounded-subset-ℝ :
      Σ ( ℝ⁰⁺ l2)
        ( λ b →
          (s : type-inhabited-totally-bounded-subset-ℝ S) →
          leq-ℝ⁰⁺ (nonnegative-abs-ℝ (pr1 s)) b)
    nonnegative-upper-bound-abs-is-in-inhabited-totally-bounded-subset-ℝ =
      ( nonnegative-max-abs-closed-interval-ℝ
          ( enclosing-closed-interval-inhabited-totally-bounded-subset-ℝ S) ,
        ( λ (s , s∈S) →
          leq-max-abs-is-in-closed-interval-ℝ
            ( enclosing-closed-interval-inhabited-totally-bounded-subset-ℝ S)
            ( s)
            ( subset-enclosing-closed-interval-inhabited-totally-bounded-subset-ℝ
              ( S)
              ( s)
              ( s∈S))))
```

## References

{{#bibliography}}
