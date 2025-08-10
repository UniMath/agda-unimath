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
open import univalent-combinatorics.pigeonhole-principle
open import univalent-combinatorics.sequences-finite-types
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
  {l : Level} (X : Subfinite-Type l)
  where

  is-dedekind-finite-type-Subfinite-Type' :
    (f : type-Subfinite-Type X → type-Subfinite-Type X) →
    is-injective f → is-equiv f
  is-dedekind-finite-type-Subfinite-Type' f is-injective-f =
    rec-trunc-Prop
      ( is-equiv-Prop f)
      ( λ j → is-dedekind-finite-subcount' j f is-injective-f)
      ( is-subfinite-type-Subfinite-Type X)

  is-dedekind-finite-type-Subfinite-Type :
    is-dedekind-finite (type-Subfinite-Type X)
  is-dedekind-finite-type-Subfinite-Type f is-emb-f =
    is-dedekind-finite-type-Subfinite-Type' f (is-injective-is-emb is-emb-f)

  dedekind-finite-type-Subfinite-Type : Dedekind-Finite-Type l
  dedekind-finite-type-Subfinite-Type =
    ( type-Subfinite-Type X , is-dedekind-finite-type-Subfinite-Type)
```

### The Cantor–Schröder–Bernstein theorem for subfinite types

If two subfinite types `X` and `Y` mutually embed, `X ↪ Y` and `Y ↪ X`, then
`X ≃ Y`.

```agda
module _
  {l1 l2 : Level} (X : Subfinite-Type l1) (Y : Subfinite-Type l2)
  where

  cantor-schröder-bernstein-Subfinite-Type :
    (type-Subfinite-Type X ↪ type-Subfinite-Type Y) →
    (type-Subfinite-Type Y ↪ type-Subfinite-Type X) →
    type-Subfinite-Type X ≃ type-Subfinite-Type Y
  cantor-schröder-bernstein-Subfinite-Type =
    cantor-schröder-bernstein-Dedekind-Finite-Type
      ( dedekind-finite-type-Subfinite-Type X)
      ( dedekind-finite-type-Subfinite-Type Y)
```

## External links

- [Finiteness in Sheaf Topoi](https://grossack.site/2024/08/19/finiteness-in-sheaf-topoi),
  blog post by Chris Grossack
- [`Fin.Kuratowski`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Fin.Kuratowski.html)
  at TypeTopology
- [finite set](https://ncatlab.org/nlab/show/finite+set) at $n$Lab
- [finite object](https://ncatlab.org/nlab/show/finite+object) at $n$Lab
- [Finite set](https://en.wikipedia.org/wiki/Finite_set) at Wikipedia
