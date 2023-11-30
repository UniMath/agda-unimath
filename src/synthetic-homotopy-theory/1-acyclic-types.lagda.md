# `1`-acyclic types

```agda
module synthetic-homotopy-theory.1-acyclic-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.binary-transport
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.0-acyclic-types
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.truncated-acyclic-maps
open import synthetic-homotopy-theory.truncated-acyclic-types
```

</details>

## Idea

We characterize the
[`1`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-types.md) as the
[`0`-connected types](foundation.0-connected-types.md).

TODO references + writing on concrete groups

## Definition

```agda
module _
  {l : Level} (A : UU l)
  where

  is-1-acyclic-Prop : Prop l
  is-1-acyclic-Prop = is-truncated-acyclic-Prop (one-𝕋) A

  is-1-acyclic : UU l
  is-1-acyclic = type-Prop is-1-acyclic-Prop

  is-prop-is-1-acyclic : is-prop is-1-acyclic
  is-prop-is-1-acyclic = is-prop-type-Prop is-1-acyclic-Prop
```

## Properties

### Every `0`-connected type is `1`-acyclic

```agda
module _
  {l : Level} (A : UU l)
  where

  is-1-acyclic-is-0-connected : is-0-connected A → is-1-acyclic A
  is-1-acyclic-is-0-connected = is-truncated-succ-acyclic-is-connected
```

### Every `1`-acyclic type is `0`-connected

TODO references + writing

```agda
private
  record
    concrete-group-assumption' {l : Level} (A : UU l) : UU (lsuc l)
    where
    field
      BG : Truncated-Type l (one-𝕋)
      pt : type-Truncated-Type BG
      η : A → type-Ω (pair (type-Truncated-Type BG) pt)
      is-injective-η : is-injective η

  concrete-group-assumption : UUω
  concrete-group-assumption =
    {l : Level} (A : UU l) → concrete-group-assumption' A

module _
  (cga : concrete-group-assumption)
  where

  is-contr-is-1-acyclic-is-set :
    {l : Level} (A : UU l) →
    is-set A → is-1-acyclic A → is-contr A
  is-contr-is-1-acyclic-is-set A s ac =
    let open concrete-group-assumption' (cga A) in
    is-contr-is-inhabited-is-prop
      ( is-prop-all-elements-equal
        ( λ x y →
          is-injective-η
            ( binary-tr
              ( Id)
              ( htpy-eq
                ( is-section-map-inv-equiv
                  ( const A (type-Ω (pair (type-Truncated-Type BG) pt)) ,
                    is-equiv-const-Id-is-acyclic-Truncated-Type A ac BG pt pt)
                  ( η))
                ( x))
              ( htpy-eq
                ( is-section-map-inv-equiv
                  ( const A (type-Ω (pair (type-Truncated-Type BG) pt)) ,
                    is-equiv-const-Id-is-acyclic-Truncated-Type A ac BG pt pt)
                  ( η))
                ( y))
              ( refl))))
      ( is-inhabited-is-0-acyclic
        ( is-truncated-acyclic-is-truncated-succ-acyclic ac))

  is-0-connected-is-1-acyclic :
    {l : Level} (A : UU l) →
    is-1-acyclic A → is-0-connected A
  is-0-connected-is-1-acyclic A ac =
    is-contr-is-1-acyclic-is-set
      ( type-trunc-Set A)
      ( is-set-type-trunc-Set)
      ( is-truncated-succ-acyclic-type-trunc-is-truncated-succ-acyclic A ac)
```

## References

TODO (use \[ and \])

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Acyclic types](synthetic-homotopy-theory.acyclic-types.md)
- [`1`-acyclic maps](synthetic-homotopy-theory.1-acyclic-maps.md)
- [`k`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-types.md)
- [`k`-acyclic maps](synthetic-homotopy-theory.truncated-acyclic-maps.md)
- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
