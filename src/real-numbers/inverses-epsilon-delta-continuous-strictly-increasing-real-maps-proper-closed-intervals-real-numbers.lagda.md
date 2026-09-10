# Inverses of ε-δ continuous strictly increasing real functions on proper closed intervals of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.inverses-epsilon-delta-continuous-strictly-increasing-real-maps-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sections
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.metric-spaces
open import metric-spaces.pointwise-epsilon-delta-continuous-maps-metric-spaces

open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.clamp-function-closed-interval-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.maps-between-proper-closed-intervals-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-approximates-of-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.real-maps-proper-closed-intervals-real-numbers
open import real-numbers.retracts-strictly-increasing-real-maps-proper-closed-intervals-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.strictly-increasing-real-maps-proper-closed-intervals-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The
[retract](real-numbers.retracts-strictly-increasing-real-maps-proper-closed-intervals-real-numbers.md)
`f⁻¹ : [f(a), f(b)] → [a, b]` of a
[strictly increasing map](real-numbers.strictly-increasing-real-maps-proper-closed-intervals-real-numbers.md)
`f : [a, b] → ℝ` on a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
satisfies the following interchange laws:

for any `x ∈ [a, b]` and `y ∈ [f(a), f(b)]`, the following propositions hold:

- `x < f⁻¹ y ⇒ f x < y`;
- `f⁻¹ y < x ⇒ y < f x`;
- `y ≤ f x ⇒ f⁻¹ y ≤ x`;
- `f x ≤ y ⇒ x ≤ f⁻¹ y`.

If `f` is
[ε-δ continuous](metric-spaces.pointwise-epsilon-delta-continuous-maps-metric-spaces.md)
at `x`, the converses hold:

- `f x < y ⇒ x < f⁻¹ y`;
- `y < f x ⇒ f⁻¹ y < x` ;
- `f⁻¹ y ≤ x ⇒ y ≤ f x` ;
- `x ≤ f⁻¹ y ⇒ f x ≤ y`.

so, if `f` is ε-δ continuous at `f⁻¹ y`, `y ≤ f (f⁻¹ y) ≤ y` and `f⁻¹` is also a
[section](foundation.sections.md) of `f`. Therefore, any ε-δ continuous strictly
increasing map `f : [a, b] → ℝ` induces an
[equivalence](foundation.equivalences.md) `[a, b] ≃ [f(a), f(b)]`.

## Propositions

### Interchange laws for strict inequality

For any `x ∈ [a, b]` and `y ∈ [f(a), f(b)]`, if `f` is ε-δ continuous at `x`,

- `f x < y ⇒ x < f⁻¹ y`;
- `y < f x ⇒ f⁻¹ y < x` .

```agda
module _
  { l l1 l2 : Level}
  { I : proper-closed-interval-ℝ l1 l2}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( l ⊔ l1 ⊔ l2)
      ( I))
  ( x@(u , lo-bound-x , hi-bound-x) :
    type-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
  ( y@(v , lo-bound-y , hi-bound-y) :
    type-im-strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( f))
  where abstract opaque
    unfolding le-ℝ

    interchange-le-right-map-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ :
      is-ε-δ-continuous-at-point-map-Metric-Space
        ( metric-space-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
        ( metric-space-ℝ (l ⊔ l1 ⊔ l2))
        ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
        ( x) →
      le-ℝ
        ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
        ( v) →
      le-ℝ
        ( u)
        ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y)
    interchange-le-right-map-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ
      cont-f Hxv =
      let
        open
          do-syntax-trunc-Prop
            ( le-prop-ℝ
              ( u)
              ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
                ( f)
                ( y)))
      in do
        ( ε , Hε) ←
          exists-ℚ⁺-in-lower-cut-is-positive-ℝ
            ( diff-ℝ
              ( v)
              ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x))
            ( is-positive-diff-le-ℝ
              { x =
                map-strictly-increasing-real-map-proper-closed-interval-ℝ f x}
              { y = v}
              ( Hxv))
        ( δ , Kδ) ← cont-f ε
        ( q , x<q , Nδxq) ← exists-rational-approximate-above-ℝ u δ
        ( p , p<q , x<p) ←
          forward-implication
            ( is-rounded-upper-cut-ℝ u q)
            ( x<q)
        ( p' , p'<p , x<p') ←
          forward-implication
            ( is-rounded-upper-cut-ℝ u p)
            ( x<p)
        let
          lemma-Nfq :
            neighborhood-ℝ (l ⊔ l1 ⊔ l2) ε
              ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l q))
          lemma-Nfq =
            Kδ
              ( clamp-proper-closed-interval-ℝ I (raise-real-ℚ l q))
              ( binary-tr
                ( neighborhood-Metric-Space
                  ( metric-space-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
                  ( δ))
                ( compute-clamp-in-closed-interval-ℝ
                  ( closed-interval-proper-closed-interval-ℝ I)
                  ( x))
                ( eq-type-subtype
                  ( subtype-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
                  { clamp-proper-closed-interval-ℝ I
                    (raise-real-ℚ (l ⊔ l1 ⊔ l2) q)}
                  { clamp-proper-closed-interval-ℝ I
                    ( raise-real-ℚ l q)}
                  ( eq-sim-ℝ
                    ( sim-clamp-closed-interval-ℝ
                      ( closed-interval-proper-closed-interval-ℝ I)
                      ( raise-real-ℚ (l ⊔ l1 ⊔ l2) q)
                      ( raise-real-ℚ l q)
                      ( sim-raise-raise-ℝ (l ⊔ l1 ⊔ l2) l (real-ℚ q)))))
                ( is-short-map-clamp-closed-interval-ℝ
                  ( closed-interval-proper-closed-interval-ℝ I)
                  ( δ)
                  ( u)
                  ( raise-real-ℚ (l ⊔ l1 ⊔ l2) q)
                  ( Nδxq)))

          lemma-leq-fq :
            leq-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l q))
              ( add-ℝ
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
                ( real-ℚ⁺ ε))
          lemma-leq-fq =
            leq-transpose-left-diff-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l q))
              ( real-ℚ⁺ ε)
              ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
              ( swap-right-diff-leq-ℝ
                ( clamp-real-map-proper-closed-interval-ℝ I
                  ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                  ( raise-real-ℚ l q))
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
                ( real-ℚ⁺ ε)
                ( reversed-diff-bound-neighborhood-ℝ ε
                  ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                    ( f)
                    ( x))
                  ( clamp-real-map-proper-closed-interval-ℝ I
                    ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                      ( f))
                    ( raise-real-ℚ l q))
                  ( lemma-Nfq)))

          lemma-le-fq-y :
            le-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l q))
              ( v)
          lemma-le-fq-y =
            concatenate-leq-le-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l q))
              ( add-ℝ
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
                ( real-ℚ⁺ ε))
              ( v)
              ( lemma-leq-fq)
              ( le-transpose-right-diff-ℝ'
                ( real-ℚ⁺ ε)
                ( v)
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
                ( le-real-is-in-lower-cut-ℝ
                  ( diff-ℝ
                    ( v)
                    ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                      ( f)
                      ( x)))
                  ( Hε)))

          lemma-lo-hi-p :
            is-in-lower-cut-ℝ
              ( upper-bound-proper-closed-interval-ℝ I)
              ( p)
          lemma-lo-hi-p =
            elim-disjunction
              ( lower-cut-ℝ (upper-bound-proper-closed-interval-ℝ I) p)
              ( id)
              ( λ hi-q →
                ex-falso
                  ( not-leq-le-ℝ
                    ( clamp-real-map-proper-closed-interval-ℝ I
                      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                        ( f))
                      ( raise-real-ℚ l q))
                    ( v)
                  ( lemma-le-fq-y)
                  ( transitive-leq-ℝ
                    ( v)
                    ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                      ( f)
                      ( raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
                        ( I)
                        ( l)))
                    ( clamp-real-map-proper-closed-interval-ℝ I
                      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                        ( f))
                      ( raise-real-ℚ l q))
                    ( is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                      ( I)
                      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                        ( f))
                      ( le-map-strictly-increasing-real-map-proper-closed-interval-ℝ
                        ( f))
                      ( _)
                      ( _)
                      ( preserves-leq-sim-ℝ
                        ( sim-raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
                          ( I)
                          ( l))
                        ( symmetric-sim-ℝ
                          ( sim-clamp-leq-upper-bound-closed-interval-ℝ
                            ( closed-interval-proper-closed-interval-ℝ I)
                            ( raise-real-ℚ l q)
                            ( preserves-leq-right-raise-ℝ
                              ( l)
                              ( leq-le-ℝ
                                ( le-real-is-in-upper-cut-ℝ
                                  ( upper-bound-proper-closed-interval-ℝ I)
                                  ( hi-q))))))
                        ( refl-leq-ℝ _)))
                    ( hi-bound-y))))
              ( is-located-lower-upper-cut-ℝ
                ( upper-bound-proper-closed-interval-ℝ I)
                ( p<q))

          lemma-leq-fpv :
            leq-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l p))
              ( v)
          lemma-leq-fpv =
            transitive-leq-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l p))
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l q))
              ( v)
              ( leq-le-ℝ lemma-le-fq-y)
              ( leq-map-clamp-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                ( I)
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( le-map-strictly-increasing-real-map-proper-closed-interval-ℝ
                  ( f))
                ( _)
                ( _)
                ( leq-raise-leq-ℝ
                  ( l)
                  ( preserves-leq-real-ℚ (leq-le-ℚ p<q))))

        intro-exists p'
          ( x<p' , intro-exists p (p'<p , lemma-lo-hi-p , lemma-leq-fpv))

    interchange-le-left-map-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ :
      is-ε-δ-continuous-at-point-map-Metric-Space
        ( metric-space-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
        ( metric-space-ℝ (l ⊔ l1 ⊔ l2))
        ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
        ( x) →
      le-ℝ
        ( v)
        ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x) →
      le-ℝ
        ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y)
        ( u)
    interchange-le-left-map-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ
      cont-f Hvx =
      let
        open
          do-syntax-trunc-Prop
            ( le-prop-ℝ
              ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
                ( f)
                ( y))
              ( u))
      in do
        ( ε , Hε) ←
          exists-ℚ⁺-in-lower-cut-is-positive-ℝ
            ( diff-ℝ
              ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
              ( v))
            ( is-positive-diff-le-ℝ
              { x = v}
              { y =
                map-strictly-increasing-real-map-proper-closed-interval-ℝ f x}
              ( Hvx))
        ( δ , Kδ) ← cont-f ε
        ( p , p<x , Nδxp) ← exists-rational-approximate-below-ℝ u δ
        ( q , p<q , q<x) ←
          forward-implication
            ( is-rounded-lower-cut-ℝ u p)
            ( p<x)
        ( q' , q<q' , q'<x) ←
          forward-implication
            ( is-rounded-lower-cut-ℝ u q)
            ( q<x)
        let
          lemma-Nfp :
            neighborhood-ℝ (l ⊔ l1 ⊔ l2) ε
              ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l p))
          lemma-Nfp =
            Kδ
              ( clamp-proper-closed-interval-ℝ I (raise-real-ℚ l p))
              ( binary-tr
                ( neighborhood-Metric-Space
                  ( metric-space-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
                  ( δ))
                ( compute-clamp-in-closed-interval-ℝ
                  ( closed-interval-proper-closed-interval-ℝ I)
                  ( x))
                ( eq-type-subtype
                  ( subtype-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
                  { clamp-proper-closed-interval-ℝ I
                    ( raise-real-ℚ (l ⊔ l1 ⊔ l2) p)}
                  { clamp-proper-closed-interval-ℝ I
                    ( raise-real-ℚ l p)}
                  ( eq-sim-ℝ
                    ( sim-clamp-closed-interval-ℝ
                      ( closed-interval-proper-closed-interval-ℝ I)
                      ( raise-real-ℚ (l ⊔ l1 ⊔ l2) p)
                      ( raise-real-ℚ l p)
                      ( sim-raise-raise-ℝ (l ⊔ l1 ⊔ l2) l (real-ℚ p)))))
                ( is-short-map-clamp-closed-interval-ℝ
                  ( closed-interval-proper-closed-interval-ℝ I)
                  ( δ)
                  ( u)
                  ( raise-real-ℚ (l ⊔ l1 ⊔ l2) p)
                  ( Nδxp)))

          lemma-leq-fp :
            leq-ℝ
              ( diff-ℝ
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
                ( real-ℚ⁺ ε))
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l p))
          lemma-leq-fp =
            swap-right-diff-leq-ℝ
              ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l p))
              ( real-ℚ⁺ ε)
              ( diff-bound-neighborhood-ℝ ε
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
                ( clamp-real-map-proper-closed-interval-ℝ I
                  ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                  ( raise-real-ℚ l p))
                ( lemma-Nfp))

          lemma-le-y-fp :
            le-ℝ
              ( v)
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l p))
          lemma-le-y-fp =
            concatenate-le-leq-ℝ
              ( v)
              ( diff-ℝ
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
                ( real-ℚ⁺ ε))
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l p))
              ( le-transpose-left-add-ℝ
                ( v)
                ( real-ℚ⁺ ε)
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
                ( tr
                  ( λ z →
                    le-ℝ
                      ( z)
                      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                        ( f)
                        ( x)))
                  ( commutative-add-ℝ _ _)
                  ( le-transpose-right-diff-ℝ
                    ( real-ℚ⁺ ε)
                    ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                      ( f)
                      ( x))
                    ( v)
                    ( le-real-is-in-lower-cut-ℝ
                      ( diff-ℝ
                        ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                          ( f)
                          ( x))
                        ( v))
                      ( Hε)))))
              ( lemma-leq-fp)

          lemma-hi-lo-q :
            is-in-upper-cut-ℝ
              ( lower-bound-proper-closed-interval-ℝ I)
              ( q)
          lemma-hi-lo-q =
            elim-disjunction
              ( upper-cut-ℝ (lower-bound-proper-closed-interval-ℝ I) q)
              ( λ lo-p →
                ex-falso
                  ( not-leq-le-ℝ
                    ( v)
                    ( clamp-real-map-proper-closed-interval-ℝ I
                      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                        ( f))
                      ( raise-real-ℚ l p))
                    ( lemma-le-y-fp)
                    ( transitive-leq-ℝ
                      ( clamp-real-map-proper-closed-interval-ℝ I
                        ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                          ( f))
                        (raise-real-ℚ l p))
                      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                        ( f)
                        ( raise-in-proper-closed-interval-lower-bound-proper-closed-interval-ℝ
                          ( I)
                          ( l)))
                      ( v)
                      ( lo-bound-y)
                      ( is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                        ( I)
                        ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                          ( f))
                        ( le-map-strictly-increasing-real-map-proper-closed-interval-ℝ
                          ( f))
                        ( _)
                        ( _)
                        ( preserves-leq-sim-ℝ
                          ( symmetric-sim-ℝ
                            ( sim-clamp-leq-lower-bound-closed-interval-ℝ
                              ( closed-interval-proper-closed-interval-ℝ I)
                              ( raise-real-ℚ l p)
                              ( preserves-leq-left-raise-ℝ
                                ( l)
                                ( leq-le-ℝ
                                  ( le-real-is-in-lower-cut-ℝ
                                    ( lower-bound-proper-closed-interval-ℝ I)
                                    ( lo-p))))))
                          ( sim-raise-in-proper-closed-interval-lower-bound-proper-closed-interval-ℝ
                            ( I)
                            ( l))
                          ( refl-leq-ℝ _))))))
              ( id)
              ( is-located-lower-upper-cut-ℝ
                ( lower-bound-proper-closed-interval-ℝ I)
                ( p<q))

          lemma-leq-fvq :
            leq-ℝ
              ( v)
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l q))
          lemma-leq-fvq =
            transitive-leq-ℝ
              ( v)
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l p))
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l q))
              ( leq-map-clamp-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                ( I)
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( le-map-strictly-increasing-real-map-proper-closed-interval-ℝ
                  ( f))
                ( _)
                ( _)
                ( leq-raise-leq-ℝ
                  ( l)
                  ( preserves-leq-real-ℚ (leq-le-ℚ p<q))))
              ( leq-le-ℝ lemma-le-y-fp)

        intro-exists q'
          ( intro-exists q (q<q' , lemma-hi-lo-q , lemma-leq-fvq) , q'<x)
```

### Interchange laws for inequality

For any `x ∈ [a, b]` and `y ∈ [f(a), f(b)]`, if `f` is ε-δ continuous at `x`,

- `f⁻¹ y ≤ x ⇒ y ≤ f x` ;
- `x ≤ f⁻¹ y ⇒ f x ≤ y`.

```agda
module _
  { l l1 l2 : Level}
  { I : proper-closed-interval-ℝ l1 l2}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( l ⊔ l1 ⊔ l2)
      ( I))
  ( x@(u , lo-bound-x , hi-bound-x) :
    type-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
  ( y@(v , lo-bound-y , hi-bound-y) :
    type-im-strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( f))
  where abstract

  interchange-leq-right-map-inv-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-ε-δ-continuous-at-point-map-Metric-Space
      ( metric-space-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
      ( metric-space-ℝ (l ⊔ l1 ⊔ l2))
      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
      ( x) →
    leq-ℝ
      ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y)
      ( u) →
    leq-ℝ
      ( v)
      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
  interchange-leq-right-map-inv-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ
    cont-f Kyu =
    leq-not-le-ℝ
      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
      ( v)
      ( map-neg
        ( interchange-le-right-map-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f)
          ( x)
          ( y)
          ( cont-f))
        ( not-le-leq-ℝ _ _ Kyu))

  interchange-leq-left-map-inv-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-ε-δ-continuous-at-point-map-Metric-Space
      ( metric-space-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
      ( metric-space-ℝ (l ⊔ l1 ⊔ l2))
      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
      ( x) →
    leq-ℝ
      ( u)
      ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y) →
    leq-ℝ
      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
      ( v)
  interchange-leq-left-map-inv-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ
    cont-f Kuy =
    leq-not-le-ℝ
      ( v)
      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
      ( map-neg
        ( interchange-le-left-map-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f)
          ( x)
          ( y)
          ( cont-f))
        ( not-le-leq-ℝ _ _ Kuy))
```

### The retraction of an ε-δ continuous strictly increasing map is a section

```agda
module _
  { l l1 l2 : Level}
  { I : proper-closed-interval-ℝ l1 l2}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( l ⊔ l1 ⊔ l2)
      ( I))
  ( cont-f :
    is-pointwise-ε-δ-continuous-map-Metric-Space
      ( metric-space-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
      ( metric-space-ℝ (l ⊔ l1 ⊔ l2))
      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f))
  where abstract

  is-section-map-inv-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-section
      ( clamp-strictly-increasing-real-map-proper-closed-interval-ℝ f)
      ( in-interval-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f))
  is-section-map-inv-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ
    y =
    eq-type-subtype
      ( subtype-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2)
        ( im-strictly-increasing-real-map-proper-closed-interval-ℝ f))
      ( antisymmetric-leq-ℝ _ _
        ( interchange-leq-left-map-inv-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f)
          ( in-interval-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( f)
            ( y))
          ( y)
          ( cont-f _)
          ( refl-leq-ℝ _))
        ( interchange-leq-right-map-inv-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f)
          ( in-interval-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( f)
            ( y))
          ( y)
          ( cont-f _)
          ( refl-leq-ℝ _)))
```

### Any ε-δ continuous strictly increasing map `[a,b] → ℝ` induces an equivalence `[a, b] ≃ [f(a) , f(b)]`

```agda
module _
  { l l1 l2 : Level}
  { I : proper-closed-interval-ℝ l1 l2}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( l ⊔ l1 ⊔ l2)
      ( I))
  ( cont-f :
    is-pointwise-ε-δ-continuous-map-Metric-Space
      ( metric-space-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
      ( metric-space-ℝ (l ⊔ l1 ⊔ l2))
      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f))
  where abstract

    is-equiv-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ :
      is-equiv (clamp-strictly-increasing-real-map-proper-closed-interval-ℝ f)
    is-equiv-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ
      =
      is-equiv-is-invertible
        ( in-interval-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f))
        ( is-section-map-inv-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f)
          ( cont-f))
        ( is-retraction-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f))
```

### The inverse of an ε-δ continuous strictly increasing map is strictly increasing

```agda
module _
  { l l1 l2 : Level}
  { I : proper-closed-interval-ℝ l1 l2}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( l ⊔ l1 ⊔ l2)
      ( I))
  ( cont-f :
    is-pointwise-ε-δ-continuous-map-Metric-Space
      ( metric-space-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
      ( metric-space-ℝ (l ⊔ l1 ⊔ l2))
      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f))
  where abstract

  preserves-le-map-inv-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ :
    ( y@(v , _ , _) y'@(v' , _ , _) :
      type-im-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( l ⊔ l1 ⊔ l2)
        ( f)) →
    le-ℝ v v' →
    le-ℝ
      ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y)
      ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y')
  preserves-le-map-inv-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ
    y@(v , lo-y , hi-y) y'@(v' , lo-y' , hi-y') Kvv' =
    let
      open
        do-syntax-trunc-Prop
          ( le-prop-ℝ
            ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( f)
              ( y))
            ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( f)
              ( y')))
    in do
      (z , lo-z , hi-z) ← dense-le-ℝ v v' Kvv'

      let
        is-in-interval-z :
          is-in-proper-closed-interval-ℝ
            ( im-strictly-increasing-real-map-proper-closed-interval-ℝ f)
            ( z)
        is-in-interval-z =
          ( leq-le-ℝ (concatenate-leq-le-ℝ _ _ _ lo-y lo-z) ,
            leq-le-ℝ (concatenate-le-leq-ℝ _ _ _ hi-z hi-y'))

        x : type-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I
        x =
          in-interval-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( f)
            ( raise-type-proper-closed-interval-ℝ
              ( im-strictly-increasing-real-map-proper-closed-interval-ℝ f)
              ( l ⊔ l1 ⊔ l2)
              ( z , is-in-interval-z))

        compute-fx :
          map-strictly-increasing-real-map-proper-closed-interval-ℝ f x ＝
          raise-ℝ (l ⊔ l1 ⊔ l2) z
        compute-fx =
          ap
            ( pr1)
            ( is-section-map-inv-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( f)
              ( cont-f)
              ( raise-type-proper-closed-interval-ℝ
                ( im-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( l ⊔ l1 ⊔ l2)
                ( z , is-in-interval-z)))

        lemma-le-y :
          le-ℝ
            ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y)
            ( pr1 x)
        lemma-le-y =
          interchange-le-left-map-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( f)
            ( x)
            ( y)
            ( cont-f x)
            ( inv-tr
              ( le-ℝ v)
              ( compute-fx)
              ( preserves-le-right-raise-ℝ (l ⊔ l1 ⊔ l2) lo-z))

        lemma-le-y' :
          le-ℝ
            ( pr1 x)
            ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( f)
              ( y'))
        lemma-le-y' =
          interchange-le-right-map-is-ε-δ-continuous-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( f)
            ( x)
            ( y')
            ( cont-f x)
            ( inv-tr
              ( λ w → le-ℝ w v')
              ( compute-fx)
              ( preserves-le-left-raise-ℝ (l ⊔ l1 ⊔ l2) hi-z))

      transitive-le-ℝ _ _ _ lemma-le-y' lemma-le-y
```
