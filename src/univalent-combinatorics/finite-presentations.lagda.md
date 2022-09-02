---
title: Finite presentations of types
---

```agda
module univalent-combinatorics.finite-presentations where
```

## Idea

Finitely presented types are types A equipped with a map f : Fin k → A such that the composite

```md
  Fin k → A → type-trunc-Set A
```

is an equivalence.
