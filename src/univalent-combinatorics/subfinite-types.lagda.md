# Subfinite types

```agda
module univalent-combinatorics.subfinite-types where
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
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.iterating-functions
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.repetitions-of-values
open import foundation.sections
open import foundation.sets
open import foundation.split-surjective-maps
open import foundation.surjective-maps
open import foundation.universe-levels

open import univalent-combinatorics.dedekind-finite-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.pigeonhole-principle
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.subcounting
```

</details>

## Idea

A type `X` is {{#concept "subfinite" Agda=is-subfinite Agda=Subfinite-Type}} if
there [exists](foundation.existential-quantification.md) an
[embedding](foundation-core.embeddings.md) into a
[standard finite type](univalent-combinatorics.standard-finite-types.md).

## Definitions

### The predicate of being subfinite

```agda
is-subfinite-Prop : {l : Level} → UU l → Prop l
is-subfinite-Prop X = trunc-Prop (subcount X)

is-subfinite : {l : Level} → UU l → UU l
is-subfinite X = type-Prop (is-subfinite-Prop X)

is-prop-is-subfinite : {l : Level} {X : UU l} → is-prop (is-subfinite X)
is-prop-is-subfinite {X = X} = is-prop-type-Prop (is-subfinite-Prop X)
```

### The subuniverse of subfinite types

```agda
Subfinite-Type : (l : Level) → UU (lsuc l)
Subfinite-Type l = Σ (UU l) (is-subfinite)

module _
  {l : Level} (X : Subfinite-Type l)
  where

  type-Subfinite-Type : UU l
  type-Subfinite-Type = pr1 X

  is-subfinite-type-Subfinite-Type : is-subfinite type-Subfinite-Type
  is-subfinite-type-Subfinite-Type = pr2 X
```

## Properties

### Subfinite types are discrete

```agda
module _
  {l : Level} (X : Subfinite-Type l)
  where

  has-decidable-equality-type-Subfinite-Type :
    has-decidable-equality (type-Subfinite-Type X)
  has-decidable-equality-type-Subfinite-Type =
    rec-trunc-Prop
      ( has-decidable-equality-Prop (type-Subfinite-Type X))
      ( λ (k , f) → has-decidable-equality-emb f (has-decidable-equality-Fin k))
      ( is-subfinite-type-Subfinite-Type X)

  discrete-type-Subfinite-Type : Discrete-Type l
  discrete-type-Subfinite-Type =
    ( type-Subfinite-Type X , has-decidable-equality-type-Subfinite-Type)
```

### Subfinite types are sets

```agda
module _
  {l : Level} (X : Subfinite-Type l)
  where

  is-set-type-Subfinite-Type : is-set (type-Subfinite-Type X)
  is-set-type-Subfinite-Type =
    is-set-has-decidable-equality (has-decidable-equality-type-Subfinite-Type X)

  set-Subfinite-Type : Set l
  set-Subfinite-Type = (type-Subfinite-Type X , is-set-type-Subfinite-Type)
```

### Subfinite types are Dedekind finite

We reproduce a proof given by
[Gro-Tsen](https://mathoverflow.net/users/17064/gro-tsen) in this MathOverflow
answer: <https://mathoverflow.net/a/433318>.

**Proof.** Let $X$ be a subfinite type witnessed by $ι : X ↪ Fin n$, and let
$f : X ↪ X$ be an arbitrary self-embedding. It suffices to prove $f$ is
surjective, so assume given an $x : X$ where we want to show there exists
$z : X$ such that $f(z) ＝ x$. The mapping $i ↦ fⁱ(x)$ defines an $ℕ$-indexed
sequence of elements of $X$. Since the
[standard pigeonhole principle](univalent-combinatorics.pigeonhole-principle.md)
applies to $\operatorname{Fin}n$ there has to be $i < j$ in
$\operatorname{Fin}n$ such that $ι(fⁱ(x)) = ι(fʲ(x))$. Since $ι$ is an embedding
we in particular have $fⁱ(x) = fʲ(x)$ . By injectivity of $f$ we can cancel $i$
applications on both sides of the equation to obtain $x = f(f^{j-i-1}(x))$, and
so $f^{j-i-1}(x)$ is our desired preimage of $x$. ∎

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

    compute-iterate-offset :
      (i d : ℕ) →
      iterate (succ-ℕ (d +ℕ i)) f x ＝ iterate i f x →
      f (iterate d f x) ＝ x
    compute-iterate-offset zero-ℕ d p = p
    compute-iterate-offset (succ-ℕ i) d p =
      compute-iterate-offset i d (is-injective-f p)

    compute-iterate-dist-f-x : f (iterate k f x) ＝ x
    compute-iterate-dist-f-x =
      compute-iterate-offset
        ( min-ℕ i j)
        ( k)
        ( ap
          ( λ i → iterate i f x)
          ( ( inv (left-successor-law-add-ℕ k (min-ℕ i j))) ∙
            ( ap (_+ℕ min-ℕ i j) compute-succ-k) ∙
            ( eq-dist-max-min-ℕ i j)) ∙
          ( compute-iterate-min-max-f-x))

  is-dedekind-finite-type-subcount' :
    (f : X → X) → is-injective f → is-equiv f
  is-dedekind-finite-type-subcount' f is-injective-f =
    is-equiv-is-split-surjective-is-injective f
      ( is-injective-f)
      ( is-split-surjective-is-injective-endo-subcount f is-injective-f)

  is-dedekind-finite-type-subcount :
    (f : X → X) → is-emb f → is-equiv f
  is-dedekind-finite-type-subcount f is-emb-f =
    is-dedekind-finite-type-subcount' f (is-injective-is-emb is-emb-f)

module _
  {l : Level} (X : Subfinite-Type l)
  where

  is-dedekind-finite-type-Subfinite-Type' :
    (f : type-Subfinite-Type X → type-Subfinite-Type X) →
    is-injective f → is-equiv f
  is-dedekind-finite-type-Subfinite-Type' f is-injective-f =
    rec-trunc-Prop
      ( is-equiv-Prop f)
      ( λ j → is-dedekind-finite-type-subcount' j f is-injective-f)
      ( is-subfinite-type-Subfinite-Type X)

  is-dedekind-finite-type-Subfinite-Type :
    is-dedekind-finite (type-Subfinite-Type X)
  is-dedekind-finite-type-Subfinite-Type f is-emb-f =
    is-dedekind-finite-type-Subfinite-Type' f (is-injective-is-emb is-emb-f)
```

## See also

- [Finite types](univalent-combinatorics.finite-types.md)
- [Dedekind finite sets](univalent-combinatorics.dedekind-finite-sets.md)
- In [`univalent-combinatorics.surjective-maps`] it is shown that if a
  Kuratowski finite set has decidable equality, then it is in fact finite.

## External links

- [Finiteness in Sheaf Topoi](https://grossack.site/2024/08/19/finiteness-in-sheaf-topoi),
  blog post by Chris Grossack
- [`Fin.Kuratowski`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Fin.Kuratowski.html)
  at TypeTopology
- [finite set](https://ncatlab.org/nlab/show/finite+set) at $n$Lab
- [finite object](https://ncatlab.org/nlab/show/finite+object) at $n$Lab
- [Finite set](https://en.wikipedia.org/wiki/Finite_set) at Wikipedia
