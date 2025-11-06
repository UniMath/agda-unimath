# Globular spheres

```agda
{-# OPTIONS --guardedness #-}

module globular-types.globular-spheres where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.unit-type
open import foundation.universe-levels

open import globular-types.empty-globular-types
open import globular-types.globular-suspension
open import globular-types.globular-types
```

</details>

## Idea

The
{{#concept "globular `n`-sphere" Disambiguation="globular type" Agda=globular-disk}}
is a [globular type](globular-types.globular-types.md) defined by iterated
[globular suspension](globular-types.globular-suspension.md) of the
[empty globular type](globular-types.empty-globular-types.md).

## Definitions

### The globular `0`-sphere

```agda
globular-0-sphere :
  Globular-Type lzero lzero
globular-0-sphere = suspension-Globular-Type empty-Globular-Type
```

### The globular `n`-sphere

```agda
globular-sphere : (n : ℕ) → Globular-Type lzero lzero
globular-sphere zero-ℕ = globular-0-sphere
globular-sphere (succ-ℕ n) = suspension-Globular-Type (globular-sphere n)
```
