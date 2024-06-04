# Torsorial type families

```agda
module foundation-core.torsorial-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.identity-types
```

</details>

## Idea

A type family `B` over `A` is said to be
{{#concept "torsorial" Disambiguation="type family" Agda=is-torsorial}} if its
[total space](foundation.dependent-pair-types.md) is
[contractible](foundation-core.contractible-types.md).

The terminology of torsorial type families is derived from torsors of
[higher group theory](higher-group-theory.md), which are type families
`X : BG → 𝒰` with contractible total space. In the conventional sense of the
word, a torsor is therefore a torsorial type family over a
[pointed connected type](higher-group-theory.higher-groups.md). If we drop the
condition that they are defined over a pointed connected type, we get to the
notion of 'torsor-like', or indeed 'torsorial' type families.

The notion of torsoriality of type families is central in many characterizations
of identity types. Indeed, the
[fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md)
shows that for any type family `B` over `A` and any `a : A`, the type family `B`
is torsorial if and only if every
[family of maps](foundation.families-of-maps.md)

```text
  (x : A) → a ＝ x → B x
```

is a [family of equivalences](foundation.families-of-equivalences.md). Indeed,
the principal example of a torsorial type family is the
[identity type](foundation-core.identity-types.md) itself. More generally, any
type family in the [connected component](foundation.connected-components.md) of
the identity type `x ↦ a ＝ x` is torsorial. These include torsors of higher
groups and [torsors](group-theory.torsors.md) of
[concrete groups](group-theory.concrete-groups.md).

Establishing torsoriality of type families is therefore one of the routine tasks
in univalent mathematics. Some files that provide general tools for establishing
torsoriality of type families include:

- [Equality of dependent function types](foundation.equality-dependent-function-types.md),
- The
  [structure identity principle](foundation.structure-identity-principle.md),
- The [subtype identity principle](foundation.subtype-identity-principle.md).

## Definition

### The predicate of being a torsorial type family

```agda
is-torsorial :
  {l1 l2 : Level} {B : UU l1} → (B → UU l2) → UU (l1 ⊔ l2)
is-torsorial E = is-contr (Σ _ E)
```

## Examples

### Identity types are torsorial

We prove two variants of the claim that
[identity types](foundation-core.identity-types.md) are torsorial:

- The type family `x ↦ a ＝ x` is torsorial, and
- The type family `x ↦ x ＝ a` is torsorial.

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-torsorial-Id : (a : A) → is-torsorial (λ x → a ＝ x)
    pr1 (pr1 (is-torsorial-Id a)) = a
    pr2 (pr1 (is-torsorial-Id a)) = refl
    pr2 (is-torsorial-Id a) (.a , refl) = refl

  abstract
    is-torsorial-Id' : (a : A) → is-torsorial (λ x → x ＝ a)
    pr1 (pr1 (is-torsorial-Id' a)) = a
    pr2 (pr1 (is-torsorial-Id' a)) = refl
    pr2 (is-torsorial-Id' a) (.a , refl) = refl
```

### See also

- [Discrete relations](foundation.discrete-relations.md) are binary torsorial
  type families.
