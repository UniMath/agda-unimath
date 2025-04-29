# Sequences in premetric spaces

```agda
module metric-spaces.sequences-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.sequences
open import foundation.universe-levels

open import metric-spaces.premetric-spaces
```

</details>

## Ideas

A
{{#concept "sequence" Disambiguation="in a premetric space" Agda=sequence-type-Premetric-Space}}
in a [premetric space](metric-spaces.premetric-spaces.md) is a
[sequence](foundation.sequences.md) in its underlying type.

## Definitions

### Sequences in premetric spaces

```agda
module _
  {l1 l2 : Level} (M : Premetric-Space l1 l2)
  where

  sequence-type-Premetric-Space : UU l1
  sequence-type-Premetric-Space = sequence (type-Premetric-Space M)
```
