# Sequential Colimits in Homotopy Type Theory

This file collects references to formalization of constructions and theorems
from {{#cite SvDR20}}.

```agda
module literature.sequential-colimits-in-homotopy-type-theory where
```

## 2 Homotopy Type Theory

The second section introduces basic notions from homotopy type theory, which we
import below for completeness.

```agda
open import foundation.universe-levels using
  ( UU
  )
open import foundation.identity-types using
  ( -- ＝ "path"
  ; refl -- "constant path"
  ; inv -- "inverse path"
  ; concat -- "concatenation of paths"
  ; assoc -- "associativity of concatenation"
  )
open import foundation.action-on-identifications-functions using
  ( ap -- "functions respect paths"
  )
open import foundation.homotopies using
  ( _~_ -- "homotopy"
  )
open import foundation.equivalences using
  ( equiv -- "equivalence"
  )
open import foundation.univalence using
  ( univalence -- "the univalence axiom"
  ; map-eq -- "function p̅ associated to a path"
  )
open import foundation.function-extensionality using
  ( funext -- "the function extensionality axiom"
  )
open import foundation.fibers-of-maps using
  ( fiber -- "the homotopy fiber of a function"
  )
open import foundation.transport-along-identifications using
  ( tr -- "transport"
  )
open import foundation.action-on-identifications-dependent-functions using
  ( apd -- "dependent functions respect paths"
  )
open import foundation.truncated-types using
  ( is-trunc -- "`n`-truncated types"
  )
open import foundation.truncations using
  ( trunc -- "the `n`-truncation of a type"
  ; unit-trunc -- "the unit map into a type's `n`-truncation"
  ; is-truncation-trunc -- "precomposing by the unit is an equivalence"
  )
open import foundation.connected-types using
  ( is-connected -- "`n`-connected types"
  )
open import foundation.truncated-maps using
  ( is-trunc-map -- "`n`-truncated functions"
  )
open import foundation.connected-maps using
  ( is-connected-map -- "`n`-connected functions"
  )
```

## 3 Sequences and Sequential Colimits

The third section defines categorical properties of sequences (which are called
_sequential diagrams_ in agda-unimath) and the colimiting functor. It concludes
by defining shifts of sequences, showing that they induce equivalences on
sequential colimits, and defines lifts of elements in a sequential diagram.

**Definition 3.1.** Sequences.

```agda
open import synthetic-homotopy-theory.sequential-diagrams using
  ( sequential-diagram
  )
```

**Definition 3.2.** Sequential colimits and their induction and recursion
principles.

Induction and recursion are given by the dependent and non-dependent universal
properties, respectively. Since we work in a setting without computational
higher inductive types, the maps induced by induction and recursion only compute
up to a path, even on points. Our homotopies in the definitions of cocones go
from left to right (i.e. `iₙ ~ iₙ₊₁ ∘ aₙ`), instead of right to left.

Our formalization works with sequential colimits specified by a cocone with a
universal property, and results about the standard construction of colimits are
obtained by specialization to the canonical cocone.

```agda
open import synthetic-homotopy-theory.sequential-colimits using
  ( standard-sequential-colimit -- the canonical colimit type
  ; map-cocone-standard-sequential-colimit -- "the canonical injection"
  ; coherence-cocone-standard-sequential-colimit -- "the glue"
  ; dup-standard-sequential-colimit -- "the induction principle"
  ; up-standard-sequential-colimit -- "the recursion principle"
  )
```

**Lemma 3.3.** Uniqueness property of the sequential colimit.

The data of a homotopy between two functions out of the standard sequential
colimit is specified by the type `htpy-out-of-standard-sequential-colimit`,
which we can then turn into a proper homotopy.

```agda
open import synthetic-homotopy-theory.sequential-colimits using
  ( htpy-out-of-standard-sequential-colimit -- data of a homotopy
  ; htpy-htpy-out-of-standard-sequential-colimit -- "data of a homotopy induces a homotopy"
  )
```

**Definition 3.4.** Natural transformations and natural equivalences between
sequential diagrams.

We call natural transformations _morphisms of sequential diagrams_, and natural
equivalences _equivalences of sequential diagrams_.

```agda
open import synthetic-homotopy-theory.morphisms-sequential-diagrams using
  ( hom-sequential-diagram -- "natural transformation"
  ; id-hom-sequential-diagram -- "identity natural transformation"
  ; comp-hom-sequential-diagram -- "composition of natural transformations"
  )
open import synthetic-homotopy-theory.equivalences-sequential-diagrams using
  ( equiv-sequential-diagram -- "natural equivalence"
  )
```

**Lemma 3.5.** Functoriality of the Sequential Colimit.

```agda
open import synthetic-homotopy-theory.functoriality-sequential-colimits using
  ( map-hom-standard-sequential-colimit -- "a natural transformation induces a map"
  ; preserves-id-map-hom-standard-sequential-colimit -- "1∞ ~ id(A∞)"
  ; preserves-comp-map-hom-standard-sequential-colimit -- "(σ ∘ τ)∞ ~ σ∞ ∘ τ∞"
  ; htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagram -- "homotopy of natural transformations induces a homotopy"
  ; equiv-equiv-standard-sequential-colimit -- "if τ is an equivalence, then τ∞ is an equivalence"
  )
```

**Lemma 3.6.** Dropping a head of a sequential diagram preserves the sequential
colimit.

**Lemma 3.7.** Dropping finitely many vertices from the beginning of a
sequential diagram preserves the sequential colimit.

Denoting by `A[k]` the sequence `A` with the first `k` vertices removed, we show
that the type of cocones under `A[k]` is equivalent to the type of cocones under
`A`, and conclude that any sequential colimit of `A[k]` also has the universal
property of a colimit of `A`. Specializing to the standard sequential colimit,
we get and equivalence `A[k]∞ ≃ A∞`.

```agda
open import synthetic-homotopy-theory.shifts-sequential-diagrams using
  ( compute-sequential-colimit-shift-sequential-diagram -- "A[k]∞ ≃ A∞"
  )
compute-sequential-colimit-shift-sequential-diagram-once =
  λ l (A : sequential-diagram l) →
    compute-sequential-colimit-shift-sequential-diagram A 1
```

## 4 Fibered Sequences

The fourth section defines fibered sequences, which we call _dependent
sequential diagrams_ in the library. It introduces the "Σ of a sequence", which
we call the _total sequential diagram_, and asks the main question about the
interplay between Σ and taking the colimit.

The paper defines fibered sequences as a family over the total space
`B : Σ ℕ A → 𝒰`, but we use the curried definition `B : (n : ℕ) → A(n) → 𝒰`.

**Definition 4.1.** Fibered sequences. Equifibered sequences.

```agda
open import synthetic-homotopy-theory.dependent-sequential-diagrams using
  ( dependent-sequential-diagram -- "A sequence (B, b) fibered over (A, a)"
  )
```

**Lemma 4.2.** The type of families over a colimit is equivalent to the type of
equifibered sequences.

This property is also called the _descent property of sequential colimits_,
because it characterizes families over a sequential colimit.

```agda
-- TODO
```

**Definition 4.3.** Σ of a fibered sequence.

```agda
open import synthetic-homotopy-theory.total-sequential-diagrams using
  ( total-sequential-diagram -- "Σ (A, a) (B, b)"
  ; pr1-total-sequential-diagram -- "the canonical projection"
  )
```

**Construction.** The equifibered family associated to a fibered sequence.

```agda
-- TODO
```

## 5 Colimits and Sums

**Theorem 5.1.** Interaction between `colim` and `Σ`.

```agda
-- TODO
```

## 6 Induction on the Sum of Sequential Colimits

```agda
-- TODO
```

## 7 Applications of the Main Theorem

**Lemma 7.1.** TODO description.

```agda
-- TODO
```

**Lemma 7.2.** Colimit of the terminal sequential diagram is contractible.

```agda
-- TODO
```

**Lemma 7.3.** Encode-decode.

This principle is called the _Fundamental theorem of identity types_ in the
library.

```agda
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
```

**Lemma 7.4.** Characterization of path spaces of images of the canonical maps
into the sequential colimit.

```agda
-- TODO
```

**Corollary 7.5.** The loop space of a sequential colimit is the sequential
colimit of loop spaces.

```agda
-- TODO
```

**Corollary 7.6.** For a morphism of sequential diagrams, the fibers of the
induced map between sequential colimits are characterized as sequential colimits
of the fibers.

```agda
-- TODO
```

**Corollary 7.7.1.** If each type in a sequential diagram is `k`-truncated, then
the colimit is `k`-truncated.

```agda
-- TODO
```

**Corollary 7.7.2.** The `k`-truncation of a sequential colimit is the
sequential colimit of `k`-truncations.

```agda
-- TODO
```

**Corollary 7.7.3.** If each type in a sequential diagram is `k`-connected, then
the colimit is `k`-connected.

```agda
-- TODO
```

**Corollary 7.7.4.** If each component of a morphism between sequential diagrams
is `k`-truncated/`k`-connected, then the induced map of sequential colimits is
`k`-truncated/`k`-connected.

```agda
-- TODO
```

**Corollary 7.7.5.** If each map in a sequential diagram is
`k`-truncated/`k`-connected, then the first injection into the colimit is
`k`-truncated/`k`-connected.

```agda
-- TODO
```
