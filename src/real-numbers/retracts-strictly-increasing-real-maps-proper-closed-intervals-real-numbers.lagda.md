# Retracts of strictly increasing real functions on proper closed intervals of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.retracts-strictly-increasing-real-maps-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.disjoint-subtypes
open import foundation.disjunction
open import foundation.double-negation
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.clamp-function-closed-interval-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-retracts-strictly-increasing-real-maps-proper-closed-intervals-real-numbers
open import real-numbers.maps-between-proper-closed-intervals-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.real-maps-proper-closed-intervals-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.strictly-increasing-real-maps-proper-closed-intervals-real-numbers
open import real-numbers.upper-retracts-strictly-increasing-real-maps-proper-closed-intervals-real-numbers
```

</details>

## Idea

For any
[strictly increasing map](real-numbers.strictly-increasing-real-maps-proper-closed-intervals-real-numbers.md)
`f : [a, b] → ℝ` on a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
and any `y : [f(a) , f(b)]`, the
[lower](real-numbers.lower-retracts-strictly-increasing-real-maps-proper-closed-intervals-real-numbers.md)
and
[upper](real-numbers.upper-retracts-strictly-increasing-real-maps-proper-closed-intervals-real-numbers.md)
retracts of `f` at `y` are [disjoint](foundation.disjoint-subtypes.md) and
located [Dedekind cuts](real-numbers.dedekind-real-numbers.md) so they define a
real map:

```text
   f⁻¹ : [f(a), f(b)] → ℝ.
```

For any `x ∈ [a, b]` and `y ∈ [f(a), f(b)]`, the following interchange laws
hold:

- `x < f⁻¹ y ⇒ f x < y`;
- `f⁻¹ y < x ⇒ y < f x`;

which imply:

- `y ≤ f x ⇒ f⁻¹ y ≤ x`;
- `f x ≤ y ⇒ x ≤ f⁻¹ y`.

In particular, for any `x ∈ [a, b]`, `x ≤ f⁻¹ (f x) ≤ x` so `f⁻¹` is a
[retraction](foundation.retractions.md) of `f`.

## Propositions

### The lower and upper retracts of a strictly increasing map are disjoint cuts

```agda
module _
  { l1 l2 l3 l4 : Level}
  { I : proper-closed-interval-ℝ l3 l4}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  ( y@(v , lo-bound , hi-bound) :
    type-im-strictly-increasing-real-map-proper-closed-interval-ℝ l2 f)
  where abstract

  is-disjoint-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
    disjoint-subtype
      ( lower-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f)
        ( y))
      ( upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f)
        ( y))
  is-disjoint-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
    r (lo , hi) =
    let open do-syntax-trunc-Prop empty-Prop
    in do
      (q , r<q , q<b , Hq) ← lo
      (s , s<r , a<s , Hs) ← hi

      let
        lemma-leq-clamp-qs :
          leq-ℝ
            ( map-clamp-proper-closed-interval-ℝ I (raise-real-ℚ l1 q))
            ( map-clamp-proper-closed-interval-ℝ I (raise-real-ℚ l1 s))
        lemma-leq-clamp-qs =
          reflects-leq-is-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( I)
            ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
            ( le-map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
            ( _)
            ( _)
            ( transitive-leq-ℝ _ _ _ Hs Hq)

        is-in-interval-s :
          is-in-proper-closed-interval-ℝ I (real-ℚ s)
        is-in-interval-s =
          ( ( leq-le-ℝ
              ( le-real-is-in-upper-cut-ℝ
                ( lower-bound-proper-closed-interval-ℝ I)
                ( a<s))) ,
            ( leq-le-ℝ
              ( transitive-le-ℝ
                ( real-ℚ s)
                ( real-ℚ q)
                ( upper-bound-proper-closed-interval-ℝ I)
                ( le-real-is-in-lower-cut-ℝ
                  ( upper-bound-proper-closed-interval-ℝ I)
                  ( q<b))
                ( preserves-le-real-ℚ (transitive-le-ℚ _ _ _ r<q s<r)))))

        is-in-interval-q :
          is-in-proper-closed-interval-ℝ I (real-ℚ q)
        is-in-interval-q =
          ( ( leq-le-ℝ
              ( transitive-le-ℝ
                ( lower-bound-proper-closed-interval-ℝ I)
                ( real-ℚ s)
                ( real-ℚ q)
                ( preserves-le-real-ℚ (transitive-le-ℚ _ _ _ r<q s<r))
                ( le-real-is-in-upper-cut-ℝ
                  ( lower-bound-proper-closed-interval-ℝ I)
                  ( a<s)))) ,
            ( leq-le-ℝ
              ( le-real-is-in-lower-cut-ℝ
                ( upper-bound-proper-closed-interval-ℝ I)
                ( q<b))))

        compute-map-clamp-s :
          sim-ℝ
            ( map-clamp-proper-closed-interval-ℝ I (raise-real-ℚ l1 s))
            ( raise-real-ℚ l1 s)
        compute-map-clamp-s =
          sim-clamp-is-in-closed-interval-ℝ
            ( closed-interval-proper-closed-interval-ℝ I)
            ( raise-real-ℚ l1 s)
            ( is-in-proper-closed-interval-sim-ℝ
              ( I)
              ( sim-raise-ℝ l1 (real-ℚ s))
              ( is-in-interval-s))

        compute-map-clamp-q :
          sim-ℝ
            ( map-clamp-proper-closed-interval-ℝ I (raise-real-ℚ l1 q))
            ( raise-real-ℚ l1 q)
        compute-map-clamp-q =
          sim-clamp-is-in-closed-interval-ℝ
            ( closed-interval-proper-closed-interval-ℝ I)
            ( raise-real-ℚ l1 q)
            ( is-in-proper-closed-interval-sim-ℝ
              ( I)
              ( sim-raise-ℝ l1 (real-ℚ q))
              ( is-in-interval-q))

        lemma-eq-clamp-qs :
          map-clamp-proper-closed-interval-ℝ I (raise-real-ℚ l1 q) ＝
          map-clamp-proper-closed-interval-ℝ I (raise-real-ℚ l1 s)
        lemma-eq-clamp-qs =
          antisymmetric-leq-ℝ _ _
            ( lemma-leq-clamp-qs)
            ( is-increasing-map-clamp-closed-interval-ℝ
              ( closed-interval-proper-closed-interval-ℝ I)
              ( _)
              ( _)
              ( preserves-leq-sim-ℝ
                ( sim-raise-ℝ l1 (real-ℚ s))
                ( sim-raise-ℝ l1 (real-ℚ q))
                ( preserves-leq-real-ℚ
                  ( leq-le-ℚ
                    ( transitive-le-ℚ _ _ _ r<q s<r)))))

        lemma-s~q : raise-real-ℚ l1 s ~ℝ raise-real-ℚ l1 q
        lemma-s~q =
          symmetric-sim-ℝ
            ( transitive-sim-ℝ _ _ _
              ( concat-eq-sim-ℝ
                ( lemma-eq-clamp-qs)
                ( compute-map-clamp-s))
              ( symmetric-sim-ℝ compute-map-clamp-q))

      not-sim-le-ℝ
        ( le-raise-le-ℝ l1
          ( preserves-le-real-ℚ (transitive-le-ℚ _ _ _ r<q s<r)))
        ( lemma-s~q)
```

### The lower and upper retracts of a strictly increasing map is a located pair of cuts

Given a strictly increasing map `f : [a, b] → ℝ` and `y ∈ [f(a), f(b)]`, for any
`q r : ℚ` with `q < r`, then either:

1. `p < a`;
2. `b < q`;
3. `∃ (r s : ℚ) | (a < r < s < b) ∧ (p < r) ∧ (s < q)`.

If `p < a` (resp `b < q`) then `p` is in the lower cut of `f⁻¹(y)` (resp. `q` is
in the upper cut of `f⁻¹(y)`).

Otherwise, (3.) implies that `f r < f s`. By cotransitivity, then either:

- `f r < v` so `p` is in the lower cut of `f⁻¹(y)`;
- `v < f s` so `q` is in the upper cut of `f⁻¹(y)`.

```agda
module _
  { l1 l2 l3 l4 : Level}
  { I : proper-closed-interval-ℝ l3 l4}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  ( y@(v , lo-bound , hi-bound) :
    type-im-strictly-increasing-real-map-proper-closed-interval-ℝ l2 f)
  where abstract

  is-located-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-located-lower-upper-ℝ
      ( lower-real-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f)
        ( y))
      ( upper-real-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f)
        ( y))
  is-located-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
    q r q<r =
    elim-disjunction
      ( ( lower-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f)
          ( y)
          ( q)) ∨
        ( upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f)
          ( y)
          ( r)))
      ( λ q<a →
        inl-disjunction
          ( is-in-lower-cut-map-inv-le-lower-bound-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( f)
            ( y)
            ( q)
            ( le-real-is-in-lower-cut-ℝ
              ( lower-bound-proper-closed-interval-ℝ I)
              ( q<a))))
      ( elim-disjunction _
        ( λ b<r →
          inr-disjunction
            ( is-in-upper-cut-map-inv-le-upper-bound-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( f)
              ( y)
              ( r)
              ( le-real-is-in-upper-cut-ℝ
                ( upper-bound-proper-closed-interval-ℝ I)
                ( b<r))))
        ( elim-exists _
          ( λ p →
            elim-exists _
              ( λ s (a<p , s<b , p<s , q<p , s<r) →
                elim-disjunction
                  ( ( lower-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
                            ( f)
                            ( y)
                            ( q)) ∨
                    ( upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
                      ( f)
                      ( y)
                      ( r)))
                  ( λ lo →
                    inl-disjunction
                      ( intro-exists p
                        ( q<p ,
                          is-in-lower-cut-le-real-ℚ
                            ( upper-bound-proper-closed-interval-ℝ I)
                            ( transitive-le-ℝ
                              ( real-ℚ p)
                              ( real-ℚ s)
                              ( upper-bound-proper-closed-interval-ℝ I)
                              ( le-real-is-in-lower-cut-ℝ
                                ( upper-bound-proper-closed-interval-ℝ I)
                                ( s<b))
                              ( preserves-le-real-ℚ p<s)) ,
                          leq-le-ℝ lo)))
                  ( λ hi →
                    inr-disjunction
                      ( intro-exists s
                        ( s<r ,
                          is-in-upper-cut-le-real-ℚ
                            ( lower-bound-proper-closed-interval-ℝ I)
                            ( transitive-le-ℝ
                              ( lower-bound-proper-closed-interval-ℝ I)
                              ( real-ℚ p)
                              ( real-ℚ s)
                              ( preserves-le-real-ℚ p<s)
                              ( le-real-is-in-upper-cut-ℝ
                                ( lower-bound-proper-closed-interval-ℝ I)
                                ( a<p))) ,
                          leq-le-ℝ hi)))
                  ( cotransitive-le-ℝ
                    ( clamp-real-map-proper-closed-interval-ℝ I
                      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                        ( f))
                      ( raise-real-ℚ l1 p))
                    ( v)
                    ( clamp-real-map-proper-closed-interval-ℝ I
                      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                        ( f))
                      ( raise-real-ℚ l1 s))
                    ( le-map-clamp-is-strictly-increasing-real-map-is-in-proper-closed-interval-ℝ
                      ( I)
                      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ
                        ( f))
                      ( le-map-strictly-increasing-real-map-proper-closed-interval-ℝ
                        ( f))
                      ( raise-real-ℚ l1 p)
                      ( raise-real-ℚ l1 s)
                      ( is-in-proper-closed-interval-sim-ℝ I
                        ( sim-raise-ℝ l1 (real-ℚ p))
                        ( ( leq-le-ℝ
                            ( le-real-is-in-upper-cut-ℝ
                              ( lower-bound-proper-closed-interval-ℝ I)
                              ( a<p))) ,
                          ( leq-le-ℝ
                            ( transitive-le-ℝ
                              ( real-ℚ p)
                              ( real-ℚ s)
                              ( upper-bound-proper-closed-interval-ℝ I)
                              ( le-real-is-in-lower-cut-ℝ
                                ( upper-bound-proper-closed-interval-ℝ I)
                                ( s<b))
                              ( preserves-le-real-ℚ p<s)))))
                      ( is-in-proper-closed-interval-sim-ℝ I
                        ( sim-raise-ℝ l1 (real-ℚ s))
                        ( ( leq-le-ℝ
                            ( transitive-le-ℝ
                              ( lower-bound-proper-closed-interval-ℝ I)
                              ( real-ℚ p)
                              ( real-ℚ s)
                              ( preserves-le-real-ℚ p<s)
                              ( le-real-is-in-upper-cut-ℝ
                                ( lower-bound-proper-closed-interval-ℝ I)
                                ( a<p)))) ,
                          ( leq-le-ℝ
                            ( le-real-is-in-lower-cut-ℝ
                              ( upper-bound-proper-closed-interval-ℝ I)
                              ( s<b)))))
                      ( le-raise-le-ℝ l1 (preserves-le-real-ℚ p<s))))))))
      ( lemma-trichotomy-le-rational-proper-closed-interval-ℝ I q r q<r)
```

## Definition

### The retract of a strictly increasing map on a proper closed interval

```agda
module _
  { l l1 l2 : Level}
  { I : proper-closed-interval-ℝ l1 l2}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( l ⊔ l1 ⊔ l2)
      ( I))
  ( y@(v , lo-bound , hi-bound) :
    type-im-strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( f))
  where

  map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
    ℝ (l ⊔ l1 ⊔ l2)
  pr1 map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ =
    lower-real-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
      ( f)
      ( y)
  pr1 (pr2 map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ) =
    upper-real-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
      ( f)
      ( y)
  pr2 (pr2 map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ) =
    ( ( is-disjoint-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f)
          ( y)) ,
      ( is-located-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f)
        ( y)))
```

## Properties

### The retraction map takes value in the original interval

```agda
module _
  { l l1 l2 : Level}
  { I : proper-closed-interval-ℝ l1 l2}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( l ⊔ l1 ⊔ l2)
      ( I))
  ( y@(v , lo-bound , hi-bound) :
    type-im-strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( f))
  where

  abstract opaque
    unfolding leq-ℝ

    leq-lower-bound-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
      leq-ℝ
        ( lower-bound-proper-closed-interval-ℝ I)
        ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y)
    leq-lower-bound-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
      q q<a =
      is-in-lower-cut-map-inv-le-lower-bound-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f)
        ( y)
        ( q)
        ( le-real-is-in-lower-cut-ℝ
          ( lower-bound-proper-closed-interval-ℝ I)
          ( q<a))

  abstract opaque
    unfolding leq-ℝ'

    leq-upper-bound-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
      leq-ℝ
        ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y)
        ( upper-bound-proper-closed-interval-ℝ I)
    leq-upper-bound-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
      =
      leq-leq'-ℝ
        ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y)
        ( upper-bound-proper-closed-interval-ℝ I)
        ( λ r b<r →
          is-in-upper-cut-map-inv-le-upper-bound-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( f)
            ( y)
            ( r)
            ( le-real-is-in-upper-cut-ℝ
              ( upper-bound-proper-closed-interval-ℝ I)
              ( b<r)))

  abstract
    is-in-interval-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
      is-in-proper-closed-interval-ℝ I
        ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y)
    is-in-interval-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
      =
      ( leq-lower-bound-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ ,
        leq-upper-bound-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ)

  in-interval-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
    type-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I
  pr1
    in-interval-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
    =
    map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y
  pr2
    in-interval-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
    =
    is-in-interval-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
```

### The retraction map is increasing

```agda
module _
  { l l1 l2 : Level}
  { I : proper-closed-interval-ℝ l1 l2}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( l ⊔ l1 ⊔ l2)
      ( I))
  ( y@(v , _ , _) y'@(v' , _ , _) :
    type-im-strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( f))
  ( y≤y' : leq-ℝ v v')
  where abstract opaque
  unfolding leq-ℝ

  preserves-leq-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
    leq-ℝ
      ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y)
      ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y')
  preserves-leq-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
    q =
    map-tot-exists
      ( λ r (q<r , r<b , Hr) →
        ( ( q<r) ,
          ( r<b) ,
          ( transitive-leq-ℝ
            ( clamp-real-map-proper-closed-interval-ℝ I
              ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
              ( raise-real-ℚ l r))
            ( v)
            ( v')
            ( y≤y')
            ( Hr))))
```

### Interchange laws for strict inequality

For any `x ∈ [a, b]` and `y ∈ [f(a), f(b)]`,

- `x < f⁻¹ y ⇒ f x < y`;
- `f⁻¹ y < x ⇒ y < f x`.

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

    interchange-le-left-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
      le-ℝ
        ( u)
        ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y) →
      le-ℝ
        ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
        ( v)
    interchange-le-left-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
      Kuy =
      let
        open
          do-syntax-trunc-Prop
            ( le-prop-ℝ
              ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
              ( v))
      in do
        (q , hi-qu , lo-qy) ← Kuy
        (r , q<r , r<b , _) ← lo-qy

        concatenate-le-leq-ℝ
          ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
          ( clamp-real-map-proper-closed-interval-ℝ I
            ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
            ( raise-real-ℚ l q))
          ( v)
          ( le-map-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( f)
            ( x)
            ( clamp-proper-closed-interval-ℝ I (raise-real-ℚ l q))
            ( preserves-le-left-sim-ℝ
              ( map-clamp-proper-closed-interval-ℝ I (raise-real-ℚ l q))
              ( map-clamp-proper-closed-interval-ℝ I u)
              ( u)
              ( sim-clamp-is-in-closed-interval-ℝ
                ( closed-interval-proper-closed-interval-ℝ I)
                ( u)
                ( lo-bound-x , hi-bound-x))
              ( le-map-clamp-le-is-in-closed-interval-ℝ
                ( closed-interval-proper-closed-interval-ℝ I)
                ( u)
                ( lo-bound-x , hi-bound-x)
                ( raise-real-ℚ l q)
                ( ( transitive-leq-ℝ
                    ( lower-bound-proper-closed-interval-ℝ I)
                    ( u)
                    ( raise-real-ℚ l q)
                    ( preserves-leq-right-raise-ℝ l
                      { x = u}
                      { y = real-ℚ q}
                      ( leq-le-ℝ (le-real-is-in-upper-cut-ℝ u hi-qu)))
                    ( lo-bound-x)) ,
                  ( preserves-leq-left-raise-ℝ l
                    { x = real-ℚ q}
                    { y = upper-bound-proper-closed-interval-ℝ I}
                    ( leq-le-ℝ
                      ( transitive-le-ℝ
                        ( real-ℚ q)
                        ( real-ℚ r)
                        ( upper-bound-proper-closed-interval-ℝ I)
                        ( le-real-is-in-lower-cut-ℝ
                          ( upper-bound-proper-closed-interval-ℝ I)
                          ( r<b))
                        ( preserves-le-real-ℚ q<r)))))
                ( preserves-le-right-raise-ℝ l
                  { u}
                  { real-ℚ q}
                  ( le-real-is-in-upper-cut-ℝ u hi-qu)))))
          ( leq-map-is-in-lower-cut-map-inv-le-lower-bound-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( f)
            ( y)
            ( q)
            ( lo-qy))

    interchange-le-right-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
      le-ℝ
        ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y)
        ( u) →
      le-ℝ
        ( v)
        ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
    interchange-le-right-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
      Kyu =
      let
        open
          do-syntax-trunc-Prop
            ( le-prop-ℝ
              ( v)
              ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x))
      in do
        (q , hi-qy , lo-qu) ← Kyu
        (p , p<q , a<p , _) ← hi-qy

        concatenate-leq-le-ℝ
          ( v)
          ( clamp-real-map-proper-closed-interval-ℝ I
            ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
            ( raise-real-ℚ l q))
          ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
          ( leq-map-is-in-upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( f)
            ( y)
            ( q)
            ( hi-qy))
          ( le-map-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( f)
            ( clamp-proper-closed-interval-ℝ I (raise-real-ℚ l q))
            ( x)
            ( preserves-le-right-sim-ℝ
              ( map-clamp-proper-closed-interval-ℝ I (raise-real-ℚ l q))
              ( map-clamp-proper-closed-interval-ℝ I u)
              ( u)
              ( sim-clamp-is-in-closed-interval-ℝ
                ( closed-interval-proper-closed-interval-ℝ I)
                ( u)
                ( lo-bound-x , hi-bound-x))
              ( le-map-clamp-le-is-in-closed-interval-ℝ
                ( closed-interval-proper-closed-interval-ℝ I)
                ( raise-real-ℚ l q)
                ( ( preserves-leq-right-raise-ℝ l
                    { x = lower-bound-proper-closed-interval-ℝ I}
                    { y = real-ℚ q}
                    ( leq-le-ℝ
                      ( transitive-le-ℝ
                        ( lower-bound-proper-closed-interval-ℝ I)
                        ( real-ℚ p)
                        ( real-ℚ q)
                        ( preserves-le-real-ℚ p<q)
                          ( le-real-is-in-upper-cut-ℝ
                          ( lower-bound-proper-closed-interval-ℝ I)
                        ( a<p))))) ,
                  ( transitive-leq-ℝ
                    ( raise-real-ℚ l q)
                    ( u)
                    ( upper-bound-proper-closed-interval-ℝ I)
                    ( hi-bound-x)
                    ( preserves-leq-left-raise-ℝ l
                      { x = real-ℚ q}
                      { y = u}
                      ( leq-le-ℝ (le-real-is-in-lower-cut-ℝ u lo-qu)))))
                ( u)
                ( lo-bound-x , hi-bound-x)
                ( preserves-le-left-raise-ℝ l
                  { real-ℚ q}
                  { u}
                  ( le-real-is-in-lower-cut-ℝ u lo-qu)))))
```

### Interchange laws for inequality

For any `x ∈ [a. b]` and `y ∈ [f(a), f(b)]`,

- `y ≤ f x ⇒ f⁻¹ y ≤ x`;
- `f x ≤ y ⇒ x ≤ f⁻¹ y`.

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

  interchange-leq-left-map-strictly-increasing-real-map-proper-closed-interval-ℝ :
    leq-ℝ
      ( v)
      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x) →
    leq-ℝ
      ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y)
      ( u)
  interchange-leq-left-map-strictly-increasing-real-map-proper-closed-interval-ℝ
    Kvx =
    leq-not-le-ℝ
      ( u)
      ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y)
      ( map-neg
        ( interchange-le-left-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f)
          ( x)
          ( y))
        ( not-le-leq-ℝ _ _ Kvx))

  interchange-leq-right-map-strictly-increasing-real-map-proper-closed-interval-ℝ :
    leq-ℝ
      ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
      ( v) →
    leq-ℝ
      ( u)
      ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y)
  interchange-leq-right-map-strictly-increasing-real-map-proper-closed-interval-ℝ
    Kxv =
    leq-not-le-ℝ
      ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f y)
      ( u)
      ( map-neg
        ( interchange-le-right-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f)
          ( x)
          ( y))
        ( not-le-leq-ℝ _ _ Kxv))
```

### The retract map **is** a retraction

```agda
module _
  { l l1 l2 : Level}
  { I : proper-closed-interval-ℝ l1 l2}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( l ⊔ l1 ⊔ l2)
      ( I))
  where abstract

  is-retraction-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-retraction
      ( clamp-strictly-increasing-real-map-proper-closed-interval-ℝ f)
      ( in-interval-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f))
  is-retraction-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
    x =
    eq-type-subtype
      ( subtype-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
      ( antisymmetric-leq-ℝ _ _
        ( interchange-leq-left-map-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f)
          ( x)
          ( clamp-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
          ( refl-leq-ℝ _))
        ( interchange-leq-right-map-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f)
          ( x)
          ( clamp-strictly-increasing-real-map-proper-closed-interval-ℝ f x)
          ( refl-leq-ℝ _)))
```

### The retraction map is surjective

```agda
module _
  { l l1 l2 : Level}
  { I : proper-closed-interval-ℝ l1 l2}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( l ⊔ l1 ⊔ l2)
      ( I))
  where abstract

  is-surjective-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-surjective
      ( in-interval-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f))
  is-surjective-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
    =
    is-surjective-has-section
      ( clamp-strictly-increasing-real-map-proper-closed-interval-ℝ f ,
        is-retraction-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f))
```

### If the retraction is strictly increasing then it's an equivalence

```agda
module _
  { l l1 l2 : Level}
  { I : proper-closed-interval-ℝ l1 l2}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( l ⊔ l1 ⊔ l2)
      ( I))
  where abstract

  is-equiv-map-inv-is-strictly-increasing-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-strictly-increasing-real-map-proper-closed-interval-ℝ
      ( im-strictly-increasing-real-map-proper-closed-interval-ℝ f)
      ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f) →
    is-equiv
      ( in-interval-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f))
  is-equiv-map-inv-is-strictly-increasing-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
    K =
    is-equiv-is-emb-is-surjective
      ( is-surjective-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f))
      ( is-emb-is-injective
        ( is-set-type-subtype
          ( subtype-proper-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I)
          ( is-set-ℝ _))
        ( λ {y} {y'} Hy →
          eq-type-subtype
            ( subtype-proper-closed-interval-ℝ
              ( l ⊔ l1 ⊔ l2)
              ( im-strictly-increasing-real-map-proper-closed-interval-ℝ f))
            ( ap
              ( pr1)
              ( is-injective-is-strictly-increasing-real-map-proper-closed-interval-ℝ
                ( im-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
                  ( f))
                ( K)
                ( ap pr1 Hy)))))
```

### If the retraction is strictly increasing then the map is an equivalence

```agda
module _
  { l l1 l2 : Level}
  { I : proper-closed-interval-ℝ l1 l2}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ
      ( l ⊔ l1 ⊔ l2)
      ( l ⊔ l1 ⊔ l2)
      ( I))
  where abstract

  is-equiv-map-is-strictly-increasing-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-strictly-increasing-real-map-proper-closed-interval-ℝ
      ( im-strictly-increasing-real-map-proper-closed-interval-ℝ f)
      ( map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ f) →
    is-equiv
      ( clamp-strictly-increasing-real-map-proper-closed-interval-ℝ f)
  is-equiv-map-is-strictly-increasing-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
    K =
    is-equiv-right-factor
      ( in-interval-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f))
      ( clamp-strictly-increasing-real-map-proper-closed-interval-ℝ f)
      ( is-equiv-map-inv-is-strictly-increasing-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f)
        ( K))
      ( is-equiv-htpy
        ( id)
        ( is-retraction-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f))
        ( is-equiv-id))
```
