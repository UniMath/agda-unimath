# Idempotents in Intensional Type Theory

This file collects references to formalization of constructions and theorems
from {{#cite Shu17}}.

```agda
module literature.idempotents-in-intensional-type-theory where
```

## 1 Introduction

The introduction section gives an introduction to the problem at hand and
motivates its study in univalent foundations.

```agda
open import group-theory.groups using
  ( Group
  )

open import higher-group-theory.higher-groups using
  ( ∞-Group
  )
```

## 2 Some notation and terminology

The second section introduces basic notions from homotopy type theory.

```agda
open import foundation.dependent-function-types -- "dependent products"

open import foundation.dependent-pair-types -- "dependent sums"

open import foundation.identity-types using
  ( _＝_ -- "identity type, its elements are paths"
  ; refl -- "the canonical elements of the identity types"
  ; concat -- "transitivity of paths"
  ; inv -- "symmetry of paths"
  ; ind-Id -- "eliminator of the identity type"
  )

open import foundation.action-on-identifications-functions using
  ( ap -- "action of functions on paths"
  ; ap-comp -- "functoriality of `ap` with respect to function composition"
  ; ap-concat -- "functoriality of `ap` with respect to transitivity of paths"
  )
```

The preferred definition for propositions in the library, `is-prop`, are types
whose identity types are [contractible](foundation-core.contractible-types.md).

```agda
open import foundation-core.propositions using
  ( all-elements-equal -- "mere proposition"
  ; is-prop -- all identity types are contractible
  )
```

The preferred definition for sets in the library, `is-set` are types whose
identity types are propositions in the preferred sense of the library. While the
same relation holds for the definitions used in the article, we note that it
does not extend one dimension lower to contractible types as our scheme does.

```agda
open import foundation-core.sets using
  ( has-uip -- "satisfies uip"
  ; is-set -- all identity types are propositions
  )

open import foundation.homotopies using
  ( _~_ -- "homotopy"
  ; nat-htpy -- "naturality of homotopies"
  )
```

The preferred notion of equivalence in the library coincides with the example
given in the article: an equivalence is a function equipped with a left inverse
and a right inverse.

```agda
open import foundation.equivalences using
  ( is-equiv -- "type of equivalence proofs"
  ; equiv -- "type of equivalences"
  ; is-property-is-equiv -- "the type of equivalence proofs is a mere proposition"
  )

open import foundation.function-extensionality using
  ( funext -- "the function extensionality axiom"
  )

open import foundation.univalence using
  ( equiv-eq -- "the canonical map `(A ＝ B) → (A ≃ B)`"
  ; univalence -- "the univalence axiom"
  )

open import foundation.propositional-truncations using
  ( ║_║₋₁ -- "propositional truncation"
  ; unit-trunc-Prop -- "the map `A → ║ A ║₋₁`"
  ; universal-property-trunc-Prop -- "the universal property of propositional truncation"
  )

open import foundation.mere-equivalences using
  ( mere-equiv -- "merely equivalent"
  )

open import foundation.univalence-implies-function-extensionality using
  ( funext-univalence -- "univalence implies function extensionality"
  )

-- MISSING: propositional truncations imply function extensionality

open import foundation.equality-cartesian-product-types using
  ( Eq-product -- observational equality on pairs
  ; equiv-pair-eq -- "characterization of the identity types of cartesian product type formation"
  )
```

## 3 Some pre-idempotents that split

In this section, definitions of "pre-idempotents", "split idempotents" and
"quasi-idempotents" are given, and basic relations between them are established.

**Definition 3.1.** Pre-idempotents.

The library's preferred terminology for "a pre-idempotent" is "an idempotent".
We reserve the terminology "a coherent idempotent" for what in the article is
referred to as "a (fully coherent) idempotent".

```agda
open import foundation.endomorphisms using
  ( endo -- "endofunction"
  )

open import foundation.idempotent-maps using
  ( is-idempotent -- "idempotency witness"
  ; idempotent-map -- "pre-idempotent (map)"
  )
```

**Definition 3.2.** Retracts and splittings.

```agda
open import foundation.retracts-of-types using
  ( retracts -- "retracts of a type"
  ; retract -- "type of retracts between two types"
  )

open import foundation.split-idempotent-maps using
  ( is-split-idempotent -- "splitting of an endofunction"
  )
```

**Lemma 3.3.** If $f$ has a splitting, then it is pre-idempotent.

```agda
open import foundation.split-idempotent-maps using
  ( is-idempotent-is-split-idempotent
  )
```

**Lemma 3.4.** The type associated to a splitting of a map is unique up to
equivalence.

```agda
open import foundation.split-idempotent-maps using
  ( essentially-unique-splitting-type-is-split-idempotent
  )
```

**Definition 3.5.** Quasi-idempotents.

The library's preferred terminology for "a quasi-idempotent" is "a quasicoherent
idempotent".

```agda
open import foundation.quasicoherently-idempotent-maps using
  ( is-quasicoherently-idempotent -- "the type of witnesses of quasi-idempotence"
  ; quasicoherently-idempotent-map -- "the type of quasi-idempotents"
  )
```

**Lemma 3.6.** If $f$ has a splitting, then it is a quasi-idempotent.

```agda
open import foundation.split-idempotent-maps using
  ( is-quasicoherently-idempotent-is-split-idempotent
  )
```

**Theorem 3.7.** If $X$ is a set, then any pre-idempotent on $X$ has a
splitting.

```agda
open import foundation.split-idempotent-maps using
  ( is-split-idempotent-is-idempotent-is-set
  )
```

**Example 3.8.**

> This example is not formalized.

**Theorem 3.9.** If a pre-idempotent is weakly constant, then it has a
splitting.

```agda
open import foundation.weakly-constant-maps using
  ( is-weakly-constant-map -- "the type of witnesses that a map is weakly constant"
  ; weakly-constant-map -- "the type of weakly constant maps"
  )

open import foundation.split-idempotent-maps using
  ( is-split-idempotent-is-weakly-constant-map-is-idempotent
  )
```

**Theorem 3.10.** An endofunction $f$ has a splitting in which the section $s$
is an embedding if and only if it is pre-idempotent and the type $f(x) = x$
admits a weakly constant endofunction for all $x$.

```agda
open import foundation.sections using
  ( is-section -- "the type of witnesses that a map is a section to a map"
  ; section -- "the type of sections of a map"
  )

open import foundation.embeddings using
  ( is-emb -- "the type of witnesses that a map is an embedding"
  ; _↪_ -- "the type of embeddings between two types"
  )
```

> The proof remains to be formalized.
> [#1103](https://github.com/UniMath/agda-unimath/issues/1103)

## 4 A pre-idempotent that doesn't split

In this section, assuming univalence and propositional truncations, an example
is given of a pre-idempotent map that does not split or extend to a
quasi-idempotent. Such a map is constructed on the
[connected component of the universe](foundation.connected-components-universes.md)
at the [cantor space](set-theory.cantor-space.md), i.e., its classifying space.

> This section remains to be formalized.
> [#1103](https://github.com/UniMath/agda-unimath/issues/1103)

**Example 4.1.** An example of an idempotence witness that cannot be extended to
a coherent system of idempotence data.

```agda
-- TODO
```

**Definition 4.2.** The Cantor space.

```agda
open import set-theory.cantor-space using
  ( cantor-space -- "C"
  )
```

**Lemma 4.3.** Assuming function extensionality, `C ≃ (C + C)`.

```agda
-- TODO
```

**Definition 4.5.** $B\operatorname{Aut}({-})$.

```agda
open import foundation.connected-components-universes using
  ( component-UU -- "BAut(-)"
  )
```

**Theorem 4.6.** There exists a pre-idempotent on $B\operatorname{Aut}(C)$ that
does not split.

```agda
-- TODO
```

**Corollary 4.7.** It is impossible to prove in MLTT that all pre-idempotents
split, or even that all pre-idempotents are quasi-idempotent.

The previous theorem shows that in MLTT with univalence and propositional
truncations the statement that all pre-idempotents split is false. Thus if it
were provable in MLTT then MLTT with univalence and propositional truncations
would be inconsistent, but it is not.

## 5 All quasi-idempotents split

In this section it is shown that, assuming function extensionality, every
quasi-idempotent map splits.

**Example 5.1.** A naïve attempt.

> This example is not formalized.

Sequential colimits of types.

```agda
open import synthetic-homotopy-theory.sequential-diagrams using
  ( sequential-diagram
  )

open import synthetic-homotopy-theory.sequential-colimits using
  ( standard-sequential-colimit
  )
```

Sequential limits of types.

```agda
open import foundation.inverse-sequential-diagrams using
  ( inverse-sequential-diagram
  )

open import foundation.sequential-limits using
  ( standard-sequential-limit
  )
```

**Lemma 5.2.** Characterization of the identity types of sequential limit
formation.

The formalization generalizes the result of the paper by considering general
inverse sequential diagrams rather than those that are constantly $f$. Also note
that compared to the paper, the coherences in the formalization are transposed.

```agda
open import foundation.sequential-limits using
  ( Eq-standard-sequential-limit -- observational equality on standard sequential limits
  ; extensionality-standard-sequential-limit
  )
```

**Theorem 5.3.** Assuming function extensionality, any quasi-idempotent splits.

```agda
open import foundation.split-idempotent-maps using
  ( is-split-idempotent-is-quasicoherently-idempotent
  )
```

**Remark 5.4.** Components of the construction.

```agda
open import foundation.split-idempotent-maps using
  ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent'
  ; splitting-type-is-quasicoherently-idempotent'
  ; inclusion-splitting-type-is-quasicoherently-idempotent'
  ; map-retraction-splitting-type-is-quasicoherently-idempotent'
  ; htpy-is-split-idempotent-is-quasicoherently-idempotent' -- "requires function extensionality"
  )
```

## 6 Splitting is a retraction

In this section it is shown, assuming the univalence axiom, that the type of
splittings of a pre-idempotent map is a retract of the type of extensions to
quasi-idempotence.

> This section remains to be formalized.
> [#1103](https://github.com/UniMath/agda-unimath/issues/1103)

**Lemma 6.3.** Characterization of the identity types of retract formation.

```agda
open import foundation.retracts-of-types using
  ( equiv-retracts -- observational equality on retracts
  ; extensionality-retracts
  )
```

## 7 Splitting is not an equivalence

In this section, it is argued that there may be more quasi-idempotence witnesses
than splittings of a map.

> This section remains to be formalized.
> [#1103](https://github.com/UniMath/agda-unimath/issues/1103)

## 8 The double classifying space of 2

In this section, an explicit example of a type with more quasi-idempotents than
splittings are worked out using the univalence axiom and propositional
truncations, proving Theorem 7.4 from the previous section.

> This section remains to be formalized.
> [#1103](https://github.com/UniMath/agda-unimath/issues/1103)

## 9 Coherent idempotents

In this section, assuming function extensionality, a "homotopy-correct"
definition of coherently idempotent maps is given.

**Definition 9.1.** (Fully coherent) idempotents.

```agda
open import foundation.coherently-idempotent-maps using
  ( is-coherently-idempotent -- "type of (fully coherent) idempotence witnesses"
  )
```

## 10 Conclusion

This section of the article features a series of 5 open problems.

> If a resolution to any of these open problems is formalized in the library,
> then it should be recorded here.

**Open Problem 10.1.** Can quasi-idempotents be split in MLTT without assuming
function extensionality? In particular, is there a more "finite" way to
construct such a splitting?

**Open Problem 10.2.** Is the map
$\operatorname{Idem}(X) → \operatorname{QIdem}(X)$ an embedding?

**Open Problem 10.3.** Is the map
$\operatorname{Idem}(X) → \operatorname{PIdem}(X)$ an embedding?

**Open Problem 10.4.** Can $\operatorname{Idem}(X)$ be defined without assuming
function extensionality?

**Open Problem 10.5.** Are there examples of other fully-coherent higher
homotopy structures that can be obtained from a finite amount of coherence by
splitting an idempotent?
