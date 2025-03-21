# Sequences in pseudometric spaces

```agda
module metric-spaces.sequences-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.sequences
open import foundation.universe-levels

open import metric-spaces.pseudometric-spaces
```

</details>

## Ideas

A
{{#concept "sequence" Disambiguation="in a pseudometric space" Agda=sequence-Pseudometric-Space}}
in a [pseudometric space](metric-spaces.pseudometricc-spaces.md) is a sequence
in its underlying type.

## Definition

### Sequences in pseudometric spaces

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  sequence-Pseudometric-Space : UU l1
  sequence-Pseudometric-Space = sequence (type-Pseudometric-Space M)
```
