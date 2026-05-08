# Postulates and assumptions

The library assumes the `--without-K` and `--exact-split` flags of Agda and
makes use of several postulates.

1. We make full use of Agda's `data` types for introducing inductive types.
2. We make full use of Agda's universe levels, including `ω`. However, it should
   be noted that most of the type constructors only define types of universe
   levels below `ω`, so a lot of the theory developed in this library does not
   apply to universe level `ω` and beyond.
3. The **function extensionality axiom** is postulated in
   [`foundation.function-extensionality`](foundation.function-extensionality.md).
4. The **univalence axiom** is postulated in
   [`foundation.univalence`](foundation.univalence.md).
5. The type theoretic **replacement axiom** is postulated in
   [`foundation.replacement`](foundation.replacement.md)
6. The **truncation operations** are postulated in
   [`foundation.truncations`](foundation.truncations.md)
7. The **interval** is postulated in
   [`synthetic-homotopy-theory.interval-type`](synthetic-homotopy-theory.interval-type.md)
8. The **circle** is postulated in
   [`synthetic-homotopy-theory.circle`](synthetic-homotopy-theory.circle.md)
9. **Pushouts** are postulated in
   [`synthetic-homotopy-theory.pushouts`](synthetic-homotopy-theory.pushouts.md)
10. **Extensionality of globular types** is postulated in
    [`globular-types.equality-globular-types`](globular-types.equality-globular-types.md).
11. Various **Agda built-in types** are postulated in
    [`primitives`](primitives.md) and in [`reflection`](reflection.md).
12. The **flat modality** and accompanying modalities, with propositional
    computation rules, are postulated in
    [`modal-type-theory`](modal-type-theory.md).

Note that there is some redundancy in the postulates we assume. For example, the
[univalence axiom implies function extensionality](foundation.univalence-implies-function-extensionality.md),
but we still assume function extensionality separately. Furthermore,
[the interval type is contractible](synthetic-homotopy-theory.interval-type.md),
and the higher inductive types in the agda-unimath library only have computation
rules up to identification, so there is no need at all to postulate it. The
[circle](synthetic-homotopy-theory.circle.md) can be constructed as the type of
`ℤ`-[torsors](group-theory.torsors.md), and the
[replacement axiom](foundation.replacement.md) can be used to prove there is a
circle in `UU lzero`. Additionally, the replacement axiom can be proven by the
join construction, which only uses
[pushouts](synthetic-homotopy-theory.pushouts.md).

With these postulates, the agda-unimath library is a library for constructive
univalent mathematics. Mathematics for which the law of excluded middle or the
axiom of choice is necessary is not yet developed in agda-unimath. However, we
are also open to any development of classical mathematics within agda-unimath,
and would welcome contributions in that direction.