# Subcounting

```agda
module univalent-combinatorics.subcounting where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.minimum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.iterating-functions
open import foundation.propositional-truncations
open import foundation.repetitions-of-values
open import foundation.sets
open import foundation.split-surjective-maps
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.sequences-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A {{#concept "subcounting" Agda=subcount}} of a type `X` is an
[embedding](foundation-core.embeddings.md) of `X` into a
[standard finite type](univalent-combinatorics.standard-finite-types.md).

**Terminology.** The term _subcounting_ is not established in the literature and
may be subject to change.

## Definitions

```agda
subcount : {l : Level} → UU l → UU l
subcount X = Σ ℕ (λ k → X ↪ Fin k)

module _
  {l : Level} {X : UU l} (e : subcount X)
  where

  bound-number-of-elements-subcount : ℕ
  bound-number-of-elements-subcount = pr1 e

  emb-subcount : X ↪ Fin bound-number-of-elements-subcount
  emb-subcount = pr2 e

  map-subcount : X → Fin bound-number-of-elements-subcount
  map-subcount = map-emb emb-subcount

  is-emb-map-subcount : is-emb map-subcount
  is-emb-map-subcount = is-emb-map-emb emb-subcount

  is-injective-map-subcount : is-injective map-subcount
  is-injective-map-subcount = is-injective-emb emb-subcount
```

## Properties

### Types with subcountings are discrete

```agda
module _
  {l : Level} {X : UU l} (e : subcount X)
  where

  is-set-has-subcount : is-set X
  is-set-has-subcount =
    is-set-emb
      ( emb-subcount e)
      ( is-set-Fin (bound-number-of-elements-subcount e))

  has-decidable-equality-has-subcount : has-decidable-equality X
  has-decidable-equality-has-subcount =
    has-decidable-equality-emb
      ( emb-subcount e)
      ( has-decidable-equality-Fin ( bound-number-of-elements-subcount e))
```

### The elements of the standard finite types can be subcounted

```agda
subcount-Fin : (k : ℕ) → subcount (Fin k)
pr1 (subcount-Fin k) = k
pr2 (subcount-Fin k) = id-emb
```

### A counting is a subcounting

```agda
subcount-count : {l : Level} {X : UU l} → count X → subcount X
subcount-count (n , e) = (n , emb-equiv (inv-equiv e))
```

### Types equipped with subcountings are closed under subtypes

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  emb-subcount-emb :
    (Y ↪ X) → (f : subcount X) → Y ↪ Fin (bound-number-of-elements-subcount f)
  emb-subcount-emb e f = comp-emb (emb-subcount f) e

  subcount-emb : (Y ↪ X) → subcount X → subcount Y
  pr1 (subcount-emb e f) = bound-number-of-elements-subcount f
  pr2 (subcount-emb e f) = emb-subcount-emb e f

  subcount-is-emb : {f : Y → X} → is-emb f → subcount X → subcount Y
  subcount-is-emb H = subcount-emb (_ , H)
```

### A type has sub-0 elements if and only if it is empty

```agda
abstract
  is-empty-is-zero-bound-number-of-elements-subcount :
    {l : Level} {X : UU l} (e : subcount X) →
    is-zero-ℕ (bound-number-of-elements-subcount e) → is-empty X
  is-empty-is-zero-bound-number-of-elements-subcount (.0 , e) refl = map-emb e
```

### If the elements of a type can be subcounted, then the elements of its propositional truncation can be subcounted

**Proof.** Given a subcounting `X ↪ Fin k`, then, by the functorial action of
propositional truncations, we have an embedding `║X║₋₁ ↪ ║Fin k║₋₁`. By
induction, if `k ≐ 0` then `║Fin k║₋₁ ≃ 0 ≃ Fin 0` and so `║X║₋₁ ↪ Fin 0` is a
subcounting. Otherwise, if `k ≐ j + 1`, then `║Fin k║₋₁ ≃ 1 ≃ Fin 1` and again
`║X║₋₁ ↪ Fin 1` is a subcounting. ∎

```agda
module _
  {l : Level} {X : UU l}
  where

  subcount-trunc-Prop : subcount X → subcount ║ X ║₋₁
  subcount-trunc-Prop (0 , f , is-emb-f) =
    ( 0 ,
      rec-trunc-Prop empty-Prop id ∘ map-trunc-Prop f ,
      is-emb-is-prop is-prop-type-trunc-Prop is-prop-empty)
  subcount-trunc-Prop (succ-ℕ k , f , is-emb-f) =
    ( 1 ,
      rec-trunc-Prop Fin-1-Prop (λ _ → inr star) ∘ map-trunc-Prop f ,
      is-emb-is-prop is-prop-type-trunc-Prop is-prop-Fin-1)
```

### Types with a subcounting are Dedekind finite

We reproduce a proof given by
[Gro-Tsen](https://mathoverflow.net/users/17064/gro-tsen) in this MathOverflow
answer: <https://mathoverflow.net/a/433318>.

**Proof.** Let $X$ be a type with a subcounting $ι : X ↪ \Fin n$, and let
$f : X ↪ X$ be an arbitrary self-embedding. It suffices to prove $f$ is
surjective, so assume given an $x : X$ where we want to show there exists
$z : X$ such that $f(z) ＝ x$. The mapping $i ↦ fⁱ(x)$ defines an $ℕ$-indexed
sequence of elements of $X$. Since the
[standard pigeonhole principle](univalent-combinatorics.pigeonhole-principle.md)
applies to $\Fin n$ there has to be $i < j$ in $\Fin n$ such that
$ι(fⁱ(x)) = ι(fʲ(x))$. Since $ι$ is an embedding we in particular have
$fⁱ(x) = fʲ(x)$ . By injectivity of $f$ we can cancel $i$ applications on both
sides of the equation to obtain $x = f(f^{j-i-1}(x))$, and so $f^{j-i-1}(x)$ is
our desired preimage of $x$. ∎

```agda
module _
  {l : Level} {X : UU l}
  where

  eq-value-min-max-eq-value-sequence :
    (f : ℕ → X) (i j : ℕ) → f i ＝ f j → f (max-ℕ i j) ＝ f (min-ℕ i j)
  eq-value-min-max-eq-value-sequence f i j p =
    rec-coproduct
      ( λ i≤j →
        ap f (leq-right-max-ℕ i j i≤j) ∙
        inv p ∙
        ap f (inv (leq-left-min-ℕ i j i≤j)))
      ( λ j≤i →
        ap f (leq-left-max-ℕ i j j≤i) ∙
        p ∙
        ap f (inv (leq-right-min-ℕ i j j≤i)))
      ( linear-leq-ℕ i j)

  compute-iterate-offset :
    (f : X → X) {x : X} → is-injective f → (i d : ℕ) →
    iterate (succ-ℕ (d +ℕ i)) f x ＝ iterate i f x →
    f (iterate d f x) ＝ x
  compute-iterate-offset f is-injective-f zero-ℕ d p = p
  compute-iterate-offset f is-injective-f (succ-ℕ i) d p =
    compute-iterate-offset f is-injective-f i d (is-injective-f p)

module _
  {l : Level} {X : UU l} (c : subcount X)
  where

  is-split-surjective-is-injective-endo-subcount :
    (f : X → X) → is-injective f → is-split-surjective f
  is-split-surjective-is-injective-endo-subcount f is-injective-f x =
    ( iterate k f x , compute-iterate-dist-f-x)
    where

    y : ℕ → Fin (bound-number-of-elements-subcount c)
    y i = map-subcount c (iterate i f x)

    r : repetition-of-values y
    r =
      repetition-of-values-sequence-Fin (bound-number-of-elements-subcount c) y

    i : ℕ
    i = first-repetition-of-values y r

    j : ℕ
    j = second-repetition-of-values y r

    k+1-nonzero : ℕ⁺
    k+1-nonzero =
      ( dist-ℕ i j , dist-neq-ℕ i j (distinction-repetition-of-values y r))

    k : ℕ
    k = pred-ℕ⁺ k+1-nonzero

    compute-succ-k : succ-ℕ k ＝ dist-ℕ i j
    compute-succ-k = ap pr1 (is-section-succ-nonzero-ℕ' k+1-nonzero)

    compute-iterate-f-x : iterate i f x ＝ iterate j f x
    compute-iterate-f-x =
      is-injective-map-subcount c
        ( is-repetition-of-values-repetition-of-values y r)

    compute-iterate-min-max-f-x :
      iterate (max-ℕ i j) f x ＝ iterate (min-ℕ i j) f x
    compute-iterate-min-max-f-x =
      eq-value-min-max-eq-value-sequence
        (λ u → iterate u f x)
        ( i)
        ( j)
        ( compute-iterate-f-x)

    compute-iterate-dist-f-x : f (iterate k f x) ＝ x
    compute-iterate-dist-f-x =
      compute-iterate-offset f is-injective-f
        ( min-ℕ i j)
        ( k)
        ( ( ap
            ( λ u → iterate u f x)
            ( ( inv (left-successor-law-add-ℕ k (min-ℕ i j))) ∙
              ( ap (_+ℕ min-ℕ i j) compute-succ-k) ∙
              ( eq-max-dist-min-ℕ i j))) ∙
          ( compute-iterate-min-max-f-x))

  is-dedekind-finite-subcount' :
    (f : X → X) → is-injective f → is-equiv f
  is-dedekind-finite-subcount' f is-injective-f =
    is-equiv-is-split-surjective-is-injective f
      ( is-injective-f)
      ( is-split-surjective-is-injective-endo-subcount f is-injective-f)

  is-dedekind-finite-subcount :
    (f : X → X) → is-emb f → is-equiv f
  is-dedekind-finite-subcount f is-emb-f =
    is-dedekind-finite-subcount' f (is-injective-is-emb is-emb-f)
```
