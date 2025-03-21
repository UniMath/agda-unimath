# Saturated carbons

```agda
module organic-chemistry.saturated-carbons where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels
open import foundation.unordered-pairs

open import organic-chemistry.hydrocarbons

open import univalent-combinatorics.finite-types
```

</details>

## Idea

An important distinguishing property of organic compounds is the presence of
double or triple carbon-carbon bonds, i.e., the presence or absence of
_unsaturated carbons_. In this module we define what it means for a carbon atom
to be saturated, and what it means for carbon atoms to have double and triple
bonds.

## Definition

```agda
module _
  {l1 l2 : Level} (H : hydrocarbon l1 l2)
  where
  is-saturated-carbon-hydrocarbon : vertex-hydrocarbon H → UU (l1 ⊔ l2)
  is-saturated-carbon-hydrocarbon c =
      (c' : vertex-hydrocarbon H) →
      is-prop (edge-hydrocarbon H (standard-unordered-pair c c'))
```

Type-theoretically, the saturation condition on a carbon atom (fix one and call
it `c`) is incarnated by asking that, for every other carbon atom `c'`, the type
of edges `c --- c'` is a proposition. Since edges incident on `c` are a subtype
of the type representing electrons of `c`, this guarantees that `c` shares no
more than 1 electron with any other carbon in the structure. An **alkane** is a
hydrocarbon such that every carbon is saturated.

```agda
  double-bond-on-hydrocarbon : vertex-hydrocarbon H → UU (l1 ⊔ l2)
  double-bond-on-hydrocarbon c = Σ (vertex-hydrocarbon H) λ c' →
    has-cardinality-ℕ 2 (edge-hydrocarbon H (standard-unordered-pair c c'))

  has-double-bond-hydrocarbon : vertex-hydrocarbon H → Prop (l1 ⊔ l2)
  has-double-bond-hydrocarbon c = trunc-Prop (double-bond-on-hydrocarbon c)

  has-triple-bond-hydrocarbon : vertex-hydrocarbon H → UU (l1 ⊔ l2)
  has-triple-bond-hydrocarbon c = Σ (vertex-hydrocarbon H) λ c' →
    has-cardinality-ℕ 3 (edge-hydrocarbon H (standard-unordered-pair c c'))
```

For a carbon atom `c` to have a double (respectively, a triple) bond, we must
find another carbon `c'` such that the type of edges `c --- c'` has cardinality
2 (respectively, 3). If all we care about is that the carbon atom has _some_
double bond, we use the truncated version. We note that, since in the graph
representation of hydrocarbons, vertices can have at most three incident edges,
if a carbon atom can have at most one triple bond.
