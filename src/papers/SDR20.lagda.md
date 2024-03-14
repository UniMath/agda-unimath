# Sequential Colimits in Homotopy Type Theory

{{#cite SDR20}}

```agda
module papers.SDR20 where
```

## 3. Sequences and Sequential Colimits

Definition 3.1: Sequences. We call sequences _sequential diagrams_.

```agda
import synthetic-homotopy-theory.sequential-diagrams using
  ( sequential-diagram)
```

Definition 3.2: Sequential colimits and their induction and recursion
principles, given by the dependent and non-dependent universal properties,
respectively. Our homotopies in the definitions of cocones go from left to
right, instead of right to left.

```agda
import synthetic-homotopy-theory.sequential-colimits using
  ( standard-sequential-colimit ;
    map-cocone-standard-sequential-colimit ;
    coherence-cocone-standard-sequential-colimit ;
    dup-standard-sequential-colimit ;
    up-standard-sequential-colimit)
```

Lemma 3.3: Uniqueness property of the sequential colimit.

```agda
import synthetic-homotopy-theory.sequential-colimits using
  ( equiv-htpy-htpy-out-of-standard-sequential-colimit ;
    htpy-htpy-out-of-standard-sequential-colimit)
```

Definition 3.4: Natural transformations and natural equivalences between
sequential diagrams. We call natural transformations _morphisms of sequential
diagrams_.

```agda
import synthetic-homotopy-theory.morphisms-sequential-diagrams using
  ( hom-sequential-diagram ;
    id-hom-sequential-diagram ;
    comp-hom-sequential-diagram)
import synthetic-homotopy-theory.equivalences-sequential-diagrams using
  ( equiv-sequential-diagram)
```

Lemma 3.5: Functoriality of the Sequential Colimit.

```agda
import synthetic-homotopy-theory.functoriality-sequential-colimits using
  ( map-hom-standard-sequential-colimit ; -- 1)
    preserves-id-map-hom-standard-sequential-colimit ; -- 2
    preserves-comp-map-hom-standard-sequential-colimit ; -- 3
    htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagram ; -- 4
    equiv-equiv-standard-sequential-colimit) -- 5
```

Lemma 3.6: Dropping a head of a sequential diagram preserves the sequential
colimit.

```agda
import synthetic-homotopy-theory.shifts-sequential-diagrams using
  ( up-cocone-shift-sequential-diagram ;
    compute-sequential-colimit-shift-sequential-diagram) -- apply to 1
```

Lemma 3.7: Dropping finitely many objects from the head of a sequential diagram
preserves the sequential colimit.

```agda
import synthetic-homotopy-theory.shifts-sequential-diagrams using
  ( compute-sequential-colimit-shift-sequential-diagram)
```

Liftings?

## 4. Fibered Sequences

Definition 4.1: Fibered sequences. In agda-unimath, a "sequence fibered over a
sequence (A, a)" is called a "dependent sequential diagram over (A, a)", and it
is defined in its curried form: instead of `B : Σ (n : ℕ) A(n) → 𝒰`, we use
`B : (n : N) → A(n) → 𝒰`.

```agda
import synthetic-homotopy-theory.dependent-sequential-diagrams using
  ( dependent-sequential-diagram)
  -- TODO?: equifibered sequences
```

Lemma 4.2: The descent property of sequential colimits

```agda
-- TODO
```

Definition 4.3: Total sequential diagram of a dependent sequential diagram.

```agda
import synthetic-homotopy-theory.total-sequential-diagrams using
  ( total-sequential-diagram ;
    pr1-total-sequential-diagram)
```

TODO: Decide how to treat (C∞, c∞).

## 5. Colimits and Sums

Theorem 5.1: Interaction between `colim` and `Σ`.

```agda
-- TODO
```

## 6. Induction on the Sum of Sequential Colimits

-- The induction principle for a sum of sequential colimits follows from the

## 7. Applications of the Main Theorem

Lemma 7.1: TODO description

```agda
-- TODO
```

Lemma 7.2: Colimit of the terminal sequential diagram is contractible

```agda
-- TODO
```

Lemma 7.3: Encode-decode. This principle is called the _Fundamental theorem of
identity types_ in the library.

```agda
import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
```

Lemma 7.4: Characterization of path spaces of images of the canonical maps into
the sequential colimit.

```agda
-- TODO
```

Corollary 7.5: The loop space of a sequential colimit is the sequential colimit
of loop spaces.

```agda
-- TODO
```

Corollary 7.6: For a morphism of sequential diagrams, the fibers of the induced
map between sequential colimits are characterized as sequential colimits of the
fibers.

```agda
-- TODO
```

Corollary 7.7.1: If each type in a sequential diagram is `k`-truncated, then the
colimit is `k`-truncated.

```agda
-- TODO
```

Corollary 7.7.2: The `k`-truncation of a sequential colimit is the sequential
colimit of `k`-truncations.

```agda
-- TODO
```

Corollary 7.7.3: If each type in a sequential diagram is `k`-connected, then the
colimit is `k`-connected.

```agda
-- TODO
```

Corollary 7.7.4: If each component of a morphism between sequential diagrams is
`k`-truncated/`k`-connected, then the induced map of sequential colimits is
`k`-truncated/`k`-connected.

```agda
-- TODO
```

Corollary 7.7.5: If each map in a sequential diagram is
`k`-truncated/`k`-connected, then the first injection into the colimit is
`k`-truncated/`k`-connected.

```agda
-- TODO
```
