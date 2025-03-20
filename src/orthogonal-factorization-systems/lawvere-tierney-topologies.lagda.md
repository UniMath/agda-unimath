# Lawvere–Tierney topologies

```agda
open import foundation.function-extensionality-axiom

module
  orthogonal-factorization-systems.lawvere-tierney-topologies
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext
open import foundation.conjunction funext
open import foundation.dependent-pair-types
open import foundation.function-types funext
open import foundation.logical-equivalences funext
open import foundation.propositional-extensionality funext
open import foundation.propositions funext
open import foundation.raising-universe-levels-unit-type funext
open import foundation.sets funext
open import foundation.subtypes funext
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A (small) {#concept "Lawvere–Tierney topology" Disambiguation="on types"} on
types is a map

```text
  j : Prop → Prop
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
module _
  {l : Level} (j : Prop l → Prop l)
  where

  is-lawvere-tierney-topology-Prop : Prop (lsuc l)
  is-lawvere-tierney-topology-Prop =
    product-Prop
      ( Π-Prop (Prop l) (λ P → j (j P) ⇔ j P))
      ( product-Prop
        ( j (raise-unit-Prop l) ⇔ unit-Prop)
        ( Π-Prop
          ( Prop l)
          ( λ P →
            Π-Prop (Prop l) (λ Q → j (P ∧ Q) ⇔ j P ∧ j Q))))

  is-lawvere-tierney-topology : UU (lsuc l)
  is-lawvere-tierney-topology = type-Prop is-lawvere-tierney-topology-Prop

  is-prop-is-lawvere-tierney-topology : is-prop is-lawvere-tierney-topology
  is-prop-is-lawvere-tierney-topology =
    is-prop-type-Prop is-lawvere-tierney-topology-Prop
```

### The set of Lawvere-Tierney topologies

```agda
lawvere-tierney-topology : (l : Level) → UU (lsuc l)
lawvere-tierney-topology l = Σ (Prop l → Prop l) (is-lawvere-tierney-topology)

is-set-lawvere-tierney-topology :
  {l : Level} → is-set (lawvere-tierney-topology l)
is-set-lawvere-tierney-topology =
  is-set-type-subtype is-lawvere-tierney-topology-Prop (is-set-subtype)

set-lawvere-tierney-topology : (l : Level) → Set (lsuc l)
set-lawvere-tierney-topology l =
  (lawvere-tierney-topology l , is-set-lawvere-tierney-topology)
```

## Examples

### The identity function on propositions defines a Lawvere–Tierney topology

```agda
is-lawvere-tierney-topology-id :
  (l : Level) → (is-lawvere-tierney-topology (id {A = Prop l}))
pr1 (is-lawvere-tierney-topology-id l) P =
  id-iff
pr1 (pr2 (is-lawvere-tierney-topology-id l)) =
  iff-equiv (inv-compute-raise-unit l)
pr2 (pr2 (is-lawvere-tierney-topology-id l)) Q P =
  id-iff

id-lawvere-tierney-topology : (l : Level) → lawvere-tierney-topology l
id-lawvere-tierney-topology l = (id , is-lawvere-tierney-topology-id l)
```

## See also

- [Large Lawvere-Tierney topologies](orthogonal-factorization-systems.large-lawvere-tierney-topologies.md)
- The
  [continuation modalities](orthogonal-factorization-systems.continuation-modalities.md)
  define Lawvere–Tierney topologies, and as a special case so does the
  [double negation modality](foundation.double-negation-modality.md).

## References

Lawvere–Tierney topologies in the context of Homotopy Type Theory are introduced
and studied in Chapter 6 of {{#cite Qui16}}.

{{#bibliography}} {{#reference Qui16}}

## External links

- [Lawvere–Tierney topology](https://ncatlab.org/nlab/show/Lawvere-Tierney+topology)
  at $n$Lab
