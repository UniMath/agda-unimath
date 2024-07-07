# Large Lawvere–Tierney topologies

```agda
module orthogonal-factorization-systems.large-lawvere-tierney-topologies where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.function-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A {#concept "Lawvere–Tierney topology" Disambiguation="on types"} on types is a
hierarchy of maps

```text
  j : {l : Level} → Prop l → Prop (δ l)
```

that is [idempotent](foundation.idempotent-maps.md) and preserves the
[unit type](foundation.unit-type.md) and
[binary products](foundation.conjunction.md)

```text
  j (j P) ≃ j P      j unit ≃ unit      j (P ∧ Q) ≃ j P ∧ j Q
```

such operations give rise to a notion of `j`-sheaves of types.

## Definitions

### The predicate on an operator on propositions of defining a Lawvere-Tierney topology

```agda
record
  is-large-lawvere-tierney-topology
    {δ : Level → Level} (j : {l : Level} → Prop l → Prop (δ l)) : UUω
  where
  field
    is-idempotent-is-large-lawvere-tierney-topology :
      {l : Level} (P : Prop l) → type-Prop (j (j P) ⇔ j P)

    preserves-unit-is-large-lawvere-tierney-topology :
      type-Prop (j unit-Prop ⇔ unit-Prop)

    preserves-conjunction-is-large-lawvere-tierney-topology :
      {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
      type-Prop (j (P ∧ Q) ⇔ j P ∧ j Q)
```

### The large set of Lawvere-Tierney topologies

```agda
record
  large-lawvere-tierney-topology (δ : Level → Level) : UUω
  where
  field
    operator-large-lawvere-tierney-topology : {l : Level} → Prop l → Prop (δ l)

    is-large-lawvere-tierney-topology-large-lawvere-tierney-topology :
      is-large-lawvere-tierney-topology operator-large-lawvere-tierney-topology
```

## Examples

### The identity large Lawvere-Tierney topology

```agda
is-large-lawvere-tierney-topology-id : is-large-lawvere-tierney-topology id
is-large-lawvere-tierney-topology-id =
  λ where
  .is-large-lawvere-tierney-topology.is-idempotent-is-large-lawvere-tierney-topology
    P →
    id-iff
  .is-large-lawvere-tierney-topology.preserves-unit-is-large-lawvere-tierney-topology →
    id-iff
  .is-large-lawvere-tierney-topology.preserves-conjunction-is-large-lawvere-tierney-topology
    P Q →
    id-iff

id-large-lawvere-tierney-topology : large-lawvere-tierney-topology (λ l → l)
id-large-lawvere-tierney-topology =
  λ where
  .large-lawvere-tierney-topology.operator-large-lawvere-tierney-topology →
    id
  .large-lawvere-tierney-topology.is-large-lawvere-tierney-topology-large-lawvere-tierney-topology →
    is-large-lawvere-tierney-topology-id
```

## See also

- [(Small) Lawvere-Tierney topologies](orthogonal-factorization-systems.lawvere-tierney-topologies.md)
- The
  [continuation modalities](orthogonal-factorization-systems.continuation-modalities.md)
  define Lawvere–Tierney topologies, and as a special case so does the
  [double negation modality](orthogonal-factorization-systems.double-negation-modality.md).

## References

Lawvere–Tierney topologies in the context of Homotopy Type Theory are introduced
and studied in Chapter 6 of {{#cite Qui16}}.

{{#bibliography}} {{#reference Qui16}}

## External links

- [Lawvere–Tierney topology](https://ncatlab.org/nlab/show/Lawvere-Tierney+topology)
  at $n$Lab
- [Lawvere–Tierney topology](https://en.wikipedia.org/wiki/Lawvere%E2%80%93Tierney_topology)
  at Wikipedia
