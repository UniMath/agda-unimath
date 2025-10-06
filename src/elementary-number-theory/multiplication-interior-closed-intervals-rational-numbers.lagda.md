# Multiplication of interior intervals of closed intervals of rational numbers

```agda
module elementary-number-theory.multiplication-interior-closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.interior-closed-intervals-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-closed-intervals-rational-numbers
open import elementary-number-theory.multiplication-nonnegative-rational-numbers
open import elementary-number-theory.multiplication-nonpositive-rational-numbers
open import elementary-number-theory.multiplication-positive-and-negative-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.negation-closed-intervals-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonpositive-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.proper-closed-intervals-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications

open import order-theory.total-orders
```

</details>

## Idea

If `[a', b']` is a
[proper](elementary-number-theory.proper-closed-intervals-rational-numbers.md)
[closed interval](elementary-number-theory.closed-intervals-rational-numbers.md)
of [rational numbers](elementary-number-theory.rational-numbers.md) and is
[interior](elementary-number-theory.interior-closed-intervals-rational-numbers.md)
to `[a, b]`, and `[c', d']` is a proper closed interval of rational numbers
interior to `[c, d]`, then the
[product](elementary-number-theory.multiplication-closed-intervals-rational-numbers.md)
of `[a', b']` and `[c', d']` is interior to the product of `[a, b]` and
`[c, d]`.

## Proof

### The sign of interval boundaries

```agda
abstract
  is-nonnegative-left-lower-bound-eq-lower-bound-mul-interval-mul-lower-bound-nontrivial-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (a<b : is-proper-closed-interval-ℚ [a,b]) →
    (c<d : is-proper-closed-interval-ℚ [c,d]) →
    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d] ＝
      ( lower-bound-closed-interval-ℚ [a,b] *ℚ
        lower-bound-closed-interval-ℚ [c,d])) →
    is-nonnegative-ℚ (lower-bound-closed-interval-ℚ [a,b])
  is-nonnegative-left-lower-bound-eq-lower-bound-mul-interval-mul-lower-bound-nontrivial-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) a<b c<d min=ac =
    rec-coproduct
      ( λ is-neg-a →
        ex-falso
          ( not-leq-le-ℚ
            ( a *ℚ d)
            ( a *ℚ c)
            ( reverses-le-left-mul-ℚ⁻ (a , is-neg-a) c d c<d)
            ( tr
              ( λ q → leq-ℚ q (a *ℚ d))
              ( min=ac)
              ( transitive-leq-ℚ _ _ _
                ( leq-right-min-ℚ _ _)
                ( leq-left-min-ℚ _ _)))))
      ( id)
      ( decide-is-negative-is-nonnegative-ℚ a)

  is-nonnegative-right-lower-bound-eq-lower-bound-mul-interval-mul-lower-bound-nontrivial-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (a<b : is-proper-closed-interval-ℚ [a,b]) →
    (c<d : is-proper-closed-interval-ℚ [c,d]) →
    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d] ＝
      ( lower-bound-closed-interval-ℚ [a,b] *ℚ
        lower-bound-closed-interval-ℚ [c,d])) →
    is-nonnegative-ℚ (lower-bound-closed-interval-ℚ [c,d])
  is-nonnegative-right-lower-bound-eq-lower-bound-mul-interval-mul-lower-bound-nontrivial-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) a<b c<d min=ac =
    rec-coproduct
      ( λ is-neg-c →
        ex-falso
          ( not-leq-le-ℚ
            ( b *ℚ c)
            ( a *ℚ c)
            ( reverses-le-right-mul-ℚ⁻ (c , is-neg-c) a b a<b)
            ( tr
              ( λ q → leq-ℚ q (b *ℚ c))
              ( min=ac)
              ( transitive-leq-ℚ _ _ _
                ( leq-left-min-ℚ _ _)
                ( leq-right-min-ℚ _ _)))))
      ( id)
      ( decide-is-negative-is-nonnegative-ℚ c)

  is-nonpositive-left-lower-bound-eq-lower-bound-mul-interval-mul-lower-upper-bound-nontrivial-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (a<b : is-proper-closed-interval-ℚ [a,b]) →
    (c<d : is-proper-closed-interval-ℚ [c,d]) →
    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d] ＝
      ( lower-bound-closed-interval-ℚ [a,b] *ℚ
        upper-bound-closed-interval-ℚ [c,d])) →
    is-nonpositive-ℚ (lower-bound-closed-interval-ℚ [a,b])
  is-nonpositive-left-lower-bound-eq-lower-bound-mul-interval-mul-lower-upper-bound-nontrivial-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) a<b c<d min=ad =
    rec-coproduct
      ( λ is-pos-a →
        ex-falso
          ( not-leq-le-ℚ
            ( a *ℚ c)
            ( a *ℚ d)
            ( preserves-le-left-mul-ℚ⁺ (a , is-pos-a) c d c<d)
            ( tr
              ( λ q → leq-ℚ q (a *ℚ c))
              ( min=ad)
              ( transitive-leq-ℚ _ _ _
                ( leq-left-min-ℚ _ _)
                ( leq-left-min-ℚ _ _)))))
      ( id)
      ( decide-is-positive-is-nonpositive-ℚ a)

  is-nonnegative-right-upper-bound-eq-lower-bound-mul-interval-mul-lower-upper-bound-nontrivial-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (a<b : is-proper-closed-interval-ℚ [a,b]) →
    (c<d : is-proper-closed-interval-ℚ [c,d]) →
    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d] ＝
      ( lower-bound-closed-interval-ℚ [a,b] *ℚ
        upper-bound-closed-interval-ℚ [c,d])) →
    is-nonnegative-ℚ (upper-bound-closed-interval-ℚ [c,d])
  is-nonnegative-right-upper-bound-eq-lower-bound-mul-interval-mul-lower-upper-bound-nontrivial-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) a<b c<d min=ad =
    rec-coproduct
      ( λ is-neg-d →
        ex-falso
          ( not-leq-le-ℚ
            ( b *ℚ d)
            ( a *ℚ d)
            ( reverses-le-right-mul-ℚ⁻ (d , is-neg-d) a b a<b)
            ( tr
              ( λ q → leq-ℚ q (b *ℚ d))
              ( min=ad)
              ( transitive-leq-ℚ _ _ _
                ( leq-right-min-ℚ _ _)
                ( leq-right-min-ℚ _ _)))))
      ( id)
      ( decide-is-negative-is-nonnegative-ℚ d)

  is-nonnegative-left-upper-bound-eq-lower-bound-mul-interval-mul-upper-lower-bound-nontrivial-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (a<b : is-proper-closed-interval-ℚ [a,b]) →
    (c<d : is-proper-closed-interval-ℚ [c,d]) →
    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d] ＝
      ( upper-bound-closed-interval-ℚ [a,b] *ℚ
        lower-bound-closed-interval-ℚ [c,d])) →
    is-nonnegative-ℚ (upper-bound-closed-interval-ℚ [a,b])
  is-nonnegative-left-upper-bound-eq-lower-bound-mul-interval-mul-upper-lower-bound-nontrivial-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) a<b c<d min=bc =
    rec-coproduct
      ( λ is-neg-b →
        ex-falso
          ( not-leq-le-ℚ
            ( b *ℚ d)
            ( b *ℚ c)
            ( reverses-le-left-mul-ℚ⁻ (b , is-neg-b) c d c<d)
            ( tr
              ( λ q → leq-ℚ q (b *ℚ d))
              ( min=bc)
              ( transitive-leq-ℚ _ _ _
                ( leq-right-min-ℚ _ _)
                ( leq-right-min-ℚ _ _)))))
      ( id)
      ( decide-is-negative-is-nonnegative-ℚ b)

  is-nonpositive-right-lower-bound-eq-lower-bound-mul-interval-mul-upper-lower-bound-nontrivial-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (a<b : is-proper-closed-interval-ℚ [a,b]) →
    (c<d : is-proper-closed-interval-ℚ [c,d]) →
    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d] ＝
      ( upper-bound-closed-interval-ℚ [a,b] *ℚ
        lower-bound-closed-interval-ℚ [c,d])) →
    is-nonpositive-ℚ (lower-bound-closed-interval-ℚ [c,d])
  is-nonpositive-right-lower-bound-eq-lower-bound-mul-interval-mul-upper-lower-bound-nontrivial-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) a<b c<d min=bc =
    rec-coproduct
      ( λ is-pos-c →
        ex-falso
          ( not-leq-le-ℚ
            ( a *ℚ c)
            ( b *ℚ c)
            ( preserves-le-right-mul-ℚ⁺ (c , is-pos-c) a b a<b)
            ( tr
              ( λ q → leq-ℚ q (a *ℚ c))
              ( min=bc)
              ( transitive-leq-ℚ _ _ _
                ( leq-left-min-ℚ _ _)
                ( leq-left-min-ℚ _ _)))))
      ( id)
      ( decide-is-positive-is-nonpositive-ℚ c)

  is-nonpositive-left-upper-bound-eq-lower-bound-mul-interval-mul-upper-bound-nontrivial-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (a<b : is-proper-closed-interval-ℚ [a,b]) →
    (c<d : is-proper-closed-interval-ℚ [c,d]) →
    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d] ＝
      ( upper-bound-closed-interval-ℚ [a,b] *ℚ
        upper-bound-closed-interval-ℚ [c,d])) →
    is-nonpositive-ℚ (upper-bound-closed-interval-ℚ [a,b])
  is-nonpositive-left-upper-bound-eq-lower-bound-mul-interval-mul-upper-bound-nontrivial-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) a<b c<d min=bd =
    rec-coproduct
      ( λ is-pos-b →
        ex-falso
          ( not-leq-le-ℚ
            ( b *ℚ c)
            ( b *ℚ d)
            ( preserves-le-left-mul-ℚ⁺ (b , is-pos-b) c d c<d)
            ( tr
              ( λ q → leq-ℚ q (b *ℚ c))
              ( min=bd)
              ( transitive-leq-ℚ _ _ _
                ( leq-left-min-ℚ _ _)
                ( leq-right-min-ℚ _ _)))))
      ( id)
      ( decide-is-positive-is-nonpositive-ℚ b)

  is-nonpositive-right-upper-bound-eq-lower-bound-mul-interval-mul-upper-bound-nontrivial-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (a<b : is-proper-closed-interval-ℚ [a,b]) →
    (c<d : is-proper-closed-interval-ℚ [c,d]) →
    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d] ＝
      ( upper-bound-closed-interval-ℚ [a,b] *ℚ
        upper-bound-closed-interval-ℚ [c,d])) →
    is-nonpositive-ℚ (upper-bound-closed-interval-ℚ [c,d])
  is-nonpositive-right-upper-bound-eq-lower-bound-mul-interval-mul-upper-bound-nontrivial-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) a<b c<d min=bd =
    rec-coproduct
      ( λ is-pos-d →
        ex-falso
          ( not-leq-le-ℚ
            ( a *ℚ d)
            ( b *ℚ d)
            ( preserves-le-right-mul-ℚ⁺ (d , is-pos-d) a b a<b)
            ( tr
              ( λ q → leq-ℚ q (a *ℚ d))
              ( min=bd)
              ( transitive-leq-ℚ _ _ _
                ( leq-right-min-ℚ _ _)
                ( leq-left-min-ℚ _ _)))))
      ( id)
      ( decide-is-positive-is-nonpositive-ℚ d)
```

### Multiplication of interior intervals

```agda
abstract
  le-lower-bound-mul-interior-closed-interval-ℚ :
    ([a,b] [c,d] [a',b'] [c',d'] : closed-interval-ℚ) →
    is-interior-closed-interval-ℚ [a,b] [a',b'] →
    is-interior-closed-interval-ℚ [c,d] [c',d'] →
    is-proper-closed-interval-ℚ [a',b'] →
    is-proper-closed-interval-ℚ [c',d'] →
    le-ℚ
      ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
      ( lower-bound-mul-closed-interval-ℚ [a',b'] [c',d'])
  le-lower-bound-mul-interior-closed-interval-ℚ
    [a,b]@((a , b) , _) [c,d]@((c , d) , _)
    [a',b']@((a' , b') , _) [c',d']@((c' , d') , _)
    (a<a' , b'<b) (c<c' , d'<d) a'<b' c'<d' =
    let
      min' = lower-bound-mul-closed-interval-ℚ [a',b'] [c',d']
      min = lower-bound-mul-closed-interval-ℚ [a,b] [c,d]
      min≤ac : leq-ℚ min (a *ℚ c)
      min≤ac = transitive-leq-ℚ _ _ _ (leq-left-min-ℚ _ _) (leq-left-min-ℚ _ _)
      min≤ad : leq-ℚ min (a *ℚ d)
      min≤ad = transitive-leq-ℚ _ _ _ (leq-right-min-ℚ _ _) (leq-left-min-ℚ _ _)
      min≤bc : leq-ℚ min (b *ℚ c)
      min≤bc = transitive-leq-ℚ _ _ _ (leq-left-min-ℚ _ _) (leq-right-min-ℚ _ _)
      min≤bd : leq-ℚ min (b *ℚ d)
      min≤bd =
        transitive-leq-ℚ _ _ _ (leq-right-min-ℚ _ _) (leq-right-min-ℚ _ _)
    in
      eq-one-of-four-min-Total-Order
        ( ℚ-Total-Order)
        ( le-ℚ-Prop min min')
        ( a' *ℚ c')
        ( a' *ℚ d')
        ( b' *ℚ c')
        ( b' *ℚ d')
        ( λ min'=a'c' →
          let
            is-nonneg-a' =
              is-nonnegative-left-lower-bound-eq-lower-bound-mul-interval-mul-lower-bound-nontrivial-closed-interval-ℚ
                ( [a',b'])
                ( [c',d'])
                ( a'<b')
                ( c'<d')
                ( min'=a'c')
            is-nonneg-c' =
              is-nonnegative-right-lower-bound-eq-lower-bound-mul-interval-mul-lower-bound-nontrivial-closed-interval-ℚ
                ( [a',b'])
                ( [c',d'])
                ( a'<b')
                ( c'<d')
                ( min'=a'c')
            is-pos-b' =
              is-positive-le-ℚ⁰⁺ (a' , is-nonneg-a') b' a'<b'
            is-pos-b = is-positive-le-ℚ⁺ (b' , is-pos-b') b b'<b
            is-pos-d' =
              is-positive-le-ℚ⁰⁺ (c' , is-nonneg-c') d' c'<d'
            is-pos-d = is-positive-le-ℚ⁺ (d' , is-pos-d') d d'<d
            is-nonneg-min' =
              inv-tr
                ( is-nonnegative-ℚ)
                ( min'=a'c')
                ( is-nonnegative-mul-ℚ a' c' is-nonneg-a' is-nonneg-c')
          in
            rec-coproduct
              ( λ is-neg-a →
                concatenate-leq-le-ℚ
                  ( min)
                  ( a *ℚ d)
                  ( min')
                  ( min≤ad)
                  ( le-negative-nonnegative-ℚ
                    ( mul-negative-positive-ℚ (a , is-neg-a) (d , is-pos-d))
                    ( min' , is-nonneg-min')))
              ( λ is-nonneg-a →
                rec-coproduct
                  ( λ is-neg-c →
                    concatenate-leq-le-ℚ
                      ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
                      ( b *ℚ c)
                      ( lower-bound-mul-closed-interval-ℚ [a',b'] [c',d'])
                      ( min≤bc)
                      ( le-negative-nonnegative-ℚ
                        ( mul-positive-negative-ℚ (b , is-pos-b) (c , is-neg-c))
                        ( min' , is-nonneg-min')))
                  ( λ is-nonneg-c →
                    concatenate-leq-le-ℚ
                      ( min)
                      ( a *ℚ c')
                      ( min')
                      ( transitive-leq-ℚ
                        ( min)
                        ( a *ℚ c)
                        ( a *ℚ c')
                        ( preserves-leq-left-mul-ℚ⁰⁺
                          ( a , is-nonneg-a)
                          ( c)
                          ( c')
                          ( leq-le-ℚ c<c'))
                        ( min≤ac))
                      ( inv-tr
                        ( le-ℚ (a *ℚ c'))
                        ( min'=a'c')
                        ( preserves-le-right-mul-ℚ⁺
                          ( c' ,
                            is-positive-le-ℚ⁰⁺
                              ( c , is-nonneg-c)
                              ( c')
                              ( c<c'))
                          ( a)
                          ( a')
                          ( a<a'))))
                  ( decide-is-negative-is-nonnegative-ℚ c))
              ( decide-is-negative-is-nonnegative-ℚ a))
        ( λ min'=a'd' →
          let
            is-nonpos-a' =
              is-nonpositive-left-lower-bound-eq-lower-bound-mul-interval-mul-lower-upper-bound-nontrivial-closed-interval-ℚ
                ( [a',b'])
                ( [c',d'])
                ( a'<b')
                ( c'<d')
                ( min'=a'd')
            is-nonneg-d' =
              is-nonnegative-right-upper-bound-eq-lower-bound-mul-interval-mul-lower-upper-bound-nontrivial-closed-interval-ℚ
                ( [a',b'])
                ( [c',d'])
                ( a'<b')
                ( c'<d')
                ( min'=a'd')
            is-neg-a =
              is-positive-le-ℚ⁰⁺ (a' , is-nonpos-a') a a<a'
            is-pos-d =
              is-positive-le-ℚ⁰⁺ (d' , is-nonneg-d') d d'<d
          in
            concatenate-leq-le-ℚ
              ( min)
              ( a *ℚ d)
              ( min')
              ( transitive-leq-ℚ _ _ _
                ( leq-right-min-ℚ _ _)
                ( leq-left-min-ℚ _ _))
              ( concatenate-le-leq-ℚ
                ( a *ℚ d)
                ( a *ℚ d')
                ( min')
                ( reverses-le-left-mul-ℚ⁻ (a , is-neg-a) d' d d'<d)
                ( inv-tr
                  ( leq-ℚ (a *ℚ d'))
                  ( min'=a'd')
                  ( preserves-leq-right-mul-ℚ⁰⁺
                    ( d' , is-nonneg-d')
                    ( a)
                    ( a')
                    ( leq-le-ℚ a<a')))))
        ( λ min'=b'c' →
          let
            is-nonneg-b' =
              is-nonnegative-left-upper-bound-eq-lower-bound-mul-interval-mul-upper-lower-bound-nontrivial-closed-interval-ℚ
                ( [a',b'])
                ( [c',d'])
                ( a'<b')
                ( c'<d')
                ( min'=b'c')
            is-nonpos-c' =
              is-nonpositive-right-lower-bound-eq-lower-bound-mul-interval-mul-upper-lower-bound-nontrivial-closed-interval-ℚ
                ( [a',b'])
                ( [c',d'])
                ( a'<b')
                ( c'<d')
                ( min'=b'c')
            is-pos-b = is-positive-le-ℚ⁰⁺ (b' , is-nonneg-b') b b'<b
            is-neg-c = is-negative-le-ℚ⁰⁻ (c' , is-nonpos-c') c c<c'
          in
            concatenate-le-leq-ℚ
              ( min)
              ( b' *ℚ c)
              ( min')
              ( concatenate-leq-le-ℚ
                ( min)
                ( b *ℚ c)
                ( b' *ℚ c)
                ( min≤bc)
                ( reverses-le-right-mul-ℚ⁻ (c , is-neg-c) b' b b'<b))
              ( inv-tr
                ( leq-ℚ (b' *ℚ c))
                ( min'=b'c')
                ( preserves-leq-left-mul-ℚ⁰⁺
                  ( b' , is-nonneg-b')
                  ( c)
                  ( c')
                  ( leq-le-ℚ c<c'))))
        ( λ min'=b'd' →
          let
            is-nonpos-b' =
              is-nonpositive-left-upper-bound-eq-lower-bound-mul-interval-mul-upper-bound-nontrivial-closed-interval-ℚ
                ( [a',b'])
                ( [c',d'])
                ( a'<b')
                ( c'<d')
                ( min'=b'd')
            is-nonpos-d' =
              is-nonpositive-right-upper-bound-eq-lower-bound-mul-interval-mul-upper-bound-nontrivial-closed-interval-ℚ
                ( [a',b'])
                ( [c',d'])
                ( a'<b')
                ( c'<d')
                ( min'=b'd')
            is-neg-a' =
              is-positive-le-ℚ⁰⁺ (b' , is-nonpos-b') a' a'<b'
            is-neg-a = is-negative-le-ℚ⁻ (a' , is-neg-a') a a<a'
            is-neg-c' =
              is-positive-le-ℚ⁰⁺ (d' , is-nonpos-d') c' c'<d'
            is-neg-c = is-negative-le-ℚ⁻ (c' , is-neg-c') c c<c'
            is-nonneg-min' =
              inv-tr
                ( is-nonnegative-ℚ)
                ( min'=b'd')
                ( is-nonnegative-mul-nonpositive-ℚ is-nonpos-b' is-nonpos-d')
          in
            rec-coproduct
              ( λ is-pos-b →
                concatenate-leq-le-ℚ
                  ( min)
                  ( b *ℚ c)
                  ( min')
                  ( min≤bc)
                  ( le-negative-nonnegative-ℚ
                    ( mul-positive-negative-ℚ (b , is-pos-b) (c , is-neg-c))
                    ( min' , is-nonneg-min')))
              ( λ is-nonpos-b →
                rec-coproduct
                  ( λ is-pos-d →
                    concatenate-leq-le-ℚ
                      ( min)
                      ( a *ℚ d)
                      ( min')
                      ( min≤ad)
                      ( le-negative-nonnegative-ℚ
                        ( mul-negative-positive-ℚ (a , is-neg-a) (d , is-pos-d))
                        ( min' , is-nonneg-min')))
                  ( λ is-nonpos-d →
                    concatenate-leq-le-ℚ
                      ( min)
                      ( b *ℚ d)
                      ( min')
                      ( min≤bd)
                      ( concatenate-leq-le-ℚ
                        ( b *ℚ d)
                        ( b' *ℚ d)
                        ( min')
                        ( reverses-leq-right-mul-ℚ⁰⁻
                          ( d , is-nonpos-d)
                          ( b')
                          ( b)
                          ( leq-le-ℚ b'<b))
                        ( inv-tr
                          ( le-ℚ (b' *ℚ d))
                          ( min'=b'd')
                          ( reverses-le-left-mul-ℚ⁻
                            ( b' ,
                              is-positive-le-ℚ⁰⁺
                                ( b , is-nonpos-b)
                                ( b')
                                ( b'<b))
                            ( d')
                            ( d)
                            ( d'<d)))))
                  ( decide-is-positive-is-nonpositive-ℚ d))
              ( decide-is-positive-is-nonpositive-ℚ b))

  le-upper-bound-mul-interior-closed-interval-ℚ :
    ([a,b] [c,d] [a',b'] [c',d'] : closed-interval-ℚ) →
    is-interior-closed-interval-ℚ [a,b] [a',b'] →
    is-interior-closed-interval-ℚ [c,d] [c',d'] →
    is-proper-closed-interval-ℚ [a',b'] →
    is-proper-closed-interval-ℚ [c',d'] →
    le-ℚ
      ( upper-bound-mul-closed-interval-ℚ [a',b'] [c',d'])
      ( upper-bound-mul-closed-interval-ℚ [a,b] [c,d])
  le-upper-bound-mul-interior-closed-interval-ℚ
    [a,b]@((a , b) , _) [c,d]@((c , d) , _)
    [a',b']@((a' , b') , _) [c',d']@((c' , d') , _)
    (a<a' , b'<b) (c<c' , d'<d) a'<b' c'<d' =
    binary-tr
      ( le-ℚ)
      ( ( ap
          ( neg-ℚ)
          ( right-negative-law-lower-bound-mul-closed-interval-ℚ
            ( [a',b'])
            ( [c',d']))) ∙
        ( neg-neg-ℚ _))
      ( ( ap
          ( neg-ℚ)
          ( right-negative-law-lower-bound-mul-closed-interval-ℚ [a,b] [c,d])) ∙
        ( neg-neg-ℚ _))
      ( neg-le-ℚ _ _
        ( le-lower-bound-mul-interior-closed-interval-ℚ
          ( [a,b])
          ( neg-closed-interval-ℚ [c,d])
          ( [a',b'])
          ( neg-closed-interval-ℚ [c',d'])
          ( a<a' , b'<b)
          ( is-interior-neg-closed-interval-ℚ [c,d] [c',d'] (c<c' , d'<d))
          ( a'<b')
          ( is-nontrivial-neg-closed-interval-ℚ [c',d'] c'<d')))

  is-interior-mul-closed-interval-ℚ :
    ([a,b] [c,d] [a',b'] [c',d'] : closed-interval-ℚ) →
    is-interior-closed-interval-ℚ [a,b] [a',b'] →
    is-interior-closed-interval-ℚ [c,d] [c',d'] →
    is-proper-closed-interval-ℚ [a',b'] →
    is-proper-closed-interval-ℚ [c',d'] →
    is-interior-closed-interval-ℚ
      ( mul-closed-interval-ℚ [a,b] [c,d])
      ( mul-closed-interval-ℚ [a',b'] [c',d'])
  is-interior-mul-closed-interval-ℚ
    [a,b] [c,d] [a',b'] [c',d'] a<a'≤b'<b c<c'≤d'<d a'<b' c'<d' =
    ( le-lower-bound-mul-interior-closed-interval-ℚ
        ( [a,b])
        ( [c,d])
        ( [a',b'])
        ( [c',d'])
        ( a<a'≤b'<b)
        ( c<c'≤d'<d)
        ( a'<b')
        ( c'<d') ,
      le-upper-bound-mul-interior-closed-interval-ℚ
        ( [a,b])
        ( [c,d])
        ( [a',b'])
        ( [c',d'])
        ( a<a'≤b'<b)
        ( c<c'≤d'<d)
        ( a'<b')
        ( c'<d'))
```
