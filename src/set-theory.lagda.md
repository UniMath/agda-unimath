# Set theory

## Idea

In univalent type theory, what we refer to formally as a _set_ is only in one
sense what is clasically understood to be a "set". Namely, we say a set is a
type whose [equality relation](foundation-core.identity-types.md) is a
[proposition](foundation-core.propositions.md). I.e., any two elements can be
equal in [at most one](foundation.subterminal-types.md) way.

However, both historically and in contemporary mathematics, what is commonly
meant by set theory is also the study of a collection of related foundational
theories whose building blocks include a _universe_ of _sets_ and a
propositionally valued _elementhood relation_ on the universe of sets.

While this elementhood relation is not built into type theory as a fundamental
construct, there is one important observable instance of it — namely, the
smallness predicate:

```text
  is-small l A := Σ (X : UU l), (A ≃ X).
```

We can say precisely that a type `A` _is an element_ of `UU l` if `A` is
`UU l`-small in this sense. Indeed, that `is-small l` is a predicate is
equivalent to the [univalence axiom](foundation-core.univalence.md). This
highlights a second connection between set theory and univalent type theory that
is incompatible with the preconception that "set theory is a study of set-level
mathematics".

In this module, we assemble ideas historically related to the study of set
theories both as foundations of set-level mathematics, but also as a study of
hierarchies in mathematics. This includes ideas such as
[cardinality](set-theory.cardinalities.md) and
[infinity](set-theory.infinite-sets.md), the
[cumulative hierarchy](set-theory.cumulative-hierarchy.md) as a model for set
theory, and [Russell's paradox](set-theory.russells-paradox.md).

## Modules in the set theory namespace

```agda
module set-theory where

open import set-theory.baire-space public
open import set-theory.cantor-space public
open import set-theory.cantors-diagonal-argument public
open import set-theory.cardinalities public
open import set-theory.countable-sets public
open import set-theory.cumulative-hierarchy public
open import set-theory.infinite-sets public
open import set-theory.russells-paradox public
open import set-theory.uncountable-sets public
```
