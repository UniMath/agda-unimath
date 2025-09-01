# Totally bounded subsets of the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.totally-bounded-subsets-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.images
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.approximations-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.nets-metric-spaces
open import metric-spaces.subspaces-metric-spaces
open import metric-spaces.totally-bounded-metric-spaces

open import order-theory.upper-bounds-large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.cauchy-completeness-dedekind-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.finitely-enumerable-subsets-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.infima-families-real-numbers
open import real-numbers.isometry-negation-real-numbers
open import real-numbers.maximum-finitely-enumerable-subsets-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.subsets-real-numbers
open import real-numbers.suprema-families-real-numbers

open import univalent-combinatorics.finitely-enumerable-subtypes
```

</details>

## Idea

A [subset of the real numbers](real-numbers.subsets-real-numbers.md) is
{{#concept "totally bounded" disambiguation="subset of the real numbers" WDID=Q1362228 WD="totally bounded space" Agda=is-totally-bounded-subset-ℝ}}
if it is [totally bounded](metric-spaces.totally-bounded-metric-spaces.md) as a
[subspace](metric-spaces.subspaces-metric-spaces.md) of the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level) (S : subset-ℝ l1 l2)
  where

  modulus-of-total-boundedness-subset-ℝ : UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
  modulus-of-total-boundedness-subset-ℝ =
    modulus-of-total-boundedness-Metric-Space l3 (metric-space-subset-ℝ S)

  is-totally-bounded-prop-subset-ℝ : Prop (l1 ⊔ lsuc l2 ⊔ lsuc l3)
  is-totally-bounded-prop-subset-ℝ =
    is-totally-bounded-prop-Metric-Space l3 (metric-space-subset-ℝ S)

  is-totally-bounded-subset-ℝ : UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
  is-totally-bounded-subset-ℝ = type-Prop is-totally-bounded-prop-subset-ℝ

totally-bounded-subset-ℝ : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
totally-bounded-subset-ℝ l1 l2 l3 =
  type-subtype (is-totally-bounded-prop-subset-ℝ {l1} {l2} l3)

module _
  {l1 l2 l3 : Level} (S : totally-bounded-subset-ℝ l1 l2 l3)
  where

  subset-totally-bounded-subset-ℝ : subset-ℝ l1 l2
  subset-totally-bounded-subset-ℝ = pr1 S

  metric-space-totally-bounded-subset-ℝ : Metric-Space (l1 ⊔ lsuc l2) l2
  metric-space-totally-bounded-subset-ℝ =
    metric-space-subset-ℝ subset-totally-bounded-subset-ℝ

  is-totally-bounded-totally-bounded-subset-ℝ :
    is-totally-bounded-subset-ℝ l3 subset-totally-bounded-subset-ℝ
  is-totally-bounded-totally-bounded-subset-ℝ = pr2 S

  is-inhabited-totally-bounded-subset-ℝ : UU (l1 ⊔ lsuc l2)
  is-inhabited-totally-bounded-subset-ℝ =
    is-inhabited-subset-ℝ subset-totally-bounded-subset-ℝ
```

## Properties

### The negation of a totally bounded subset of ℝ is totally bounded

```agda
module _
  {l1 l2 l3 : Level} (S : totally-bounded-subset-ℝ l1 l2 l3)
  where

  abstract
    is-totally-bounded-neg-totally-bounded-subset-ℝ :
      is-totally-bounded-subset-ℝ
        ( l1 ⊔ lsuc l2 ⊔ l3)
        ( neg-subset-ℝ (subset-totally-bounded-subset-ℝ S))
    is-totally-bounded-neg-totally-bounded-subset-ℝ =
      preserves-is-totally-bounded-isometric-equiv-Metric-Space _ _
        ( is-totally-bounded-im-isometry-is-totally-bounded-Metric-Space
          ( metric-space-totally-bounded-subset-ℝ S)
          ( metric-space-ℝ l2)
          ( is-totally-bounded-totally-bounded-subset-ℝ S)
          ( comp-isometry-Metric-Space
            ( metric-space-totally-bounded-subset-ℝ S)
            ( metric-space-ℝ l2)
            ( metric-space-ℝ l2)
            ( isometry-neg-ℝ)
            ( isometry-inclusion-subspace-Metric-Space
              ( metric-space-ℝ l2)
              ( subset-totally-bounded-subset-ℝ S))))
        ( isometric-equiv-neg-subset-im-neg-subset-ℝ
          ( subset-totally-bounded-subset-ℝ S))

  neg-totally-bounded-subset-ℝ :
    totally-bounded-subset-ℝ l1 l2 (l1 ⊔ lsuc l2 ⊔ l3)
  neg-totally-bounded-subset-ℝ =
    ( neg-subset-ℝ (subset-totally-bounded-subset-ℝ S) ,
      is-totally-bounded-neg-totally-bounded-subset-ℝ)
```

### Inhabited, totally bounded subsets of ℝ have a supremum

This proof is adapted from Theorem 11.5.7 of {{#cite UF13}}.

```agda
module _
  {l1 l2 l3 : Level} (S : subset-ℝ l1 l2) (|S| : is-inhabited-subtype S)
  (M : modulus-of-total-boundedness-subset-ℝ l3 S)
  where

  private
    net : ℚ⁺ → finitely-enumerable-subset-ℝ (l1 ⊔ lsuc l2 ⊔ l3) l2
    net δ =
      finitely-enumerable-subtype-im-finitely-enumerable-subtype
        ( inclusion-subset-ℝ S)
        ( finitely-enumerable-subset-net-Metric-Space
          ( metric-space-subset-ℝ S)
          ( δ)
          ( M δ))

    is-net :
      (δ : ℚ⁺) →
      is-approximation-Metric-Space
        ( metric-space-subset-ℝ S)
        ( δ)
        ( subtype-finitely-enumerable-subtype (pr1 (M δ)))
    is-net δ = pr2 (M δ)

    net⊆S :
      (δ : ℚ⁺) → (subset-finitely-enumerable-subset-ℝ (net δ)) ⊆ S
    net⊆S δ n =
      rec-trunc-Prop
        ( S n)
        ( λ z → tr (type-Prop ∘ S) (pr2 z) (pr2 (pr1 (pr1 z))))

    is-inhabited-net :
      (δ : ℚ⁺) →
      is-inhabited-finitely-enumerable-subset-ℝ (net δ)
    is-inhabited-net δ =
      map-is-inhabited
        ( map-unit-im (pr1 ∘ pr1))
        ( is-inhabited-net-inhabited-Metric-Space
          ( metric-space-subset-ℝ S)
          ( |S|)
          ( δ)
          ( M δ))

    max-net : ℚ⁺ → ℝ l2
    max-net δ =
      max-inhabited-finitely-enumerable-subset-ℝ
        ( net δ)
        ( is-inhabited-net δ)

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
              ( is-inhabited-net ε)
              ( max-net η +ℝ real-ℚ⁺ η))
            ( λ (z , z∈net-ε) →
              let
                open
                  do-syntax-trunc-Prop
                    ( leq-ℝ-Prop z (max-net η +ℝ real-ℚ⁺ η))
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
                      ( is-inhabited-net η)
                      ( map-unit-im (pr1 ∘ pr1) ((y , y∈S) , y∈net-η))))
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
                            ( is-inhabited-net ε')
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
                le-ℝ-Prop
                  ( sup-modulated-totally-bounded-subset-ℝ -ℝ real-ℚ⁺ ε)
                  ( s)))
      in do
        (ε' , ε'+ε'<ε) ← double-le-ℚ⁺ ε
        ((x , x∈net-ε') , max-net-ε'-ε'<x) ←
          is-approximated-below-max-inhabited-finitely-enumerable-subset-ℝ
            ( net ε')
            ( is-inhabited-net ε') ε'
        intro-exists
          (x , net⊆S ε' x x∈net-ε')
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
              ( tr (λ y → leq-ℝ y (max-net ε' -ℝ real-ℚ⁺ ε'))
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
  (S : totally-bounded-subset-ℝ l1 l2 l3)
  (|S| : is-inhabited-totally-bounded-subset-ℝ S)
  where

  abstract
    has-supremum-inhabited-totally-bounded-subset-ℝ :
      has-supremum-subset-ℝ (subset-totally-bounded-subset-ℝ S) l2
    has-supremum-inhabited-totally-bounded-subset-ℝ =
      rec-trunc-Prop
        ( has-supremum-prop-subset-ℝ (subset-totally-bounded-subset-ℝ S) l2)
        ( has-supremum-modulated-totally-bounded-subset-ℝ
          ( subset-totally-bounded-subset-ℝ S)
          ( |S|))
        ( is-totally-bounded-totally-bounded-subset-ℝ S)

    sup-inhabited-totally-bounded-subset-ℝ : ℝ l2
    sup-inhabited-totally-bounded-subset-ℝ =
      pr1 has-supremum-inhabited-totally-bounded-subset-ℝ

    is-supremum-sup-inhabited-totally-bounded-subset-ℝ :
      is-supremum-subset-ℝ
        ( subset-totally-bounded-subset-ℝ S)
        ( sup-inhabited-totally-bounded-subset-ℝ)
    is-supremum-sup-inhabited-totally-bounded-subset-ℝ =
      pr2 has-supremum-inhabited-totally-bounded-subset-ℝ
```

### Inhabited, totally bounded subsets of ℝ have an infimum

```agda
module _
  {l1 l2 l3 : Level}
  (S : totally-bounded-subset-ℝ l1 l2 l3)
  (|S| : is-inhabited-totally-bounded-subset-ℝ S)
  where

  abstract
    inf-inhabited-totally-bounded-subset-ℝ : ℝ l2
    inf-inhabited-totally-bounded-subset-ℝ =
      neg-ℝ
        ( sup-inhabited-totally-bounded-subset-ℝ
          ( neg-totally-bounded-subset-ℝ S)
          ( neg-is-inhabited-subset-ℝ (subset-totally-bounded-subset-ℝ S) |S|))

    is-infimum-inf-inhabited-totally-bounded-subset-ℝ :
      is-infimum-subset-ℝ
        ( subset-totally-bounded-subset-ℝ S)
        ( inf-inhabited-totally-bounded-subset-ℝ)
    is-infimum-inf-inhabited-totally-bounded-subset-ℝ =
      is-infimum-neg-supremum-neg-subset-ℝ
        ( subset-totally-bounded-subset-ℝ S)
        ( sup-inhabited-totally-bounded-subset-ℝ
          ( neg-totally-bounded-subset-ℝ S)
          ( neg-is-inhabited-subset-ℝ (pr1 S) |S|))
        ( is-supremum-sup-inhabited-totally-bounded-subset-ℝ
          ( neg-totally-bounded-subset-ℝ S)
          ( neg-is-inhabited-subset-ℝ (subset-totally-bounded-subset-ℝ S) |S|))

    has-infimum-inhabited-totally-bounded-subset-ℝ :
      has-infimum-subset-ℝ (subset-totally-bounded-subset-ℝ S) l2
    has-infimum-inhabited-totally-bounded-subset-ℝ =
      ( inf-inhabited-totally-bounded-subset-ℝ ,
        is-infimum-inf-inhabited-totally-bounded-subset-ℝ)
```

## References

{{#bibliography}}
