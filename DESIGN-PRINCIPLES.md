
# Design of the library

## Postulates in the library

The `agda-unimath` library is a library of formalized mathematics in vanilla Agda. Throughout our library, we assume the `--without-K` and `--exact-split` flags of Agda. Furthermore, we assume some postulates.

1. We make full use of Agda's `data` types for introducing inductive types.
2. We make full use of Agda's universe levels, including `ω`. However, it should be noted that most of the type constructors only define types of universe levels below `ω`, so a lot of the theory developed in this library does not apply to universe level `ω` and beyond.
3. The **function extensionality axiom** is postulated in [`foundation-core.function-extensionality`](https://unimath.github.io/agda-unimath/foundation-core.function-extensionality.html).
4. The **univalence axiom** is postulated in [`foundation-core.univalence`](https://unimath.github.io/agda-unimath/foundation-core.univalence.html).
5. The type theoretic **replacement axiom** is postulated in [`foundation.replacement`](https://unimath.github.io/agda-unimath/foundation.replacement.html)
6. The **truncation operations** are postulated in [`foundation.truncations`](https://unimath.github.io/agda-unimath/foundation.truncations.html)
7. The **interval** is postulated in [`synthetic-homotopy-theory.interval-type`](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.interval-type.html)
8. The **circle** is postulated in [`synthetic-homotopy-theory.circle`](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.circle.html)
9. **Pushouts** are postulated in [`synthetic-homotopy-theory.pushouts`](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.pushouts.html)

Note that there is some redundancy in the postulates we assume. For example, the [univalence axiom implies function extensionality](https://unimath.github.io/agda-unimath/foundation.univalence-implies-function-extensionality.html), but we still assume function extensionality separately. Furthermore, The interval type is contractible, so there is no need at all to postulate it. The circle can be constructed as the type of `ℤ`-torsors, and the replacement axiom can be used to prove there is a circle in `UU lzero`. Finally, the replacement axiom can be proven by the join construction, which only uses pushouts.

We also note that the higher inductive types in the `agda-unimath` library only have computation rules up to identification.

With these postulates, the `agda-unimath` library is a library for constructive univalent mathematics. Mathematics for which the law of excluded middle or the axiom of choice is necessary is not yet developed in `agda-unimath`. However, we are also open to any development of classical mathematics within `agda-unimath`, and we do also welcome contributions in that direction.

## Structure of the library

1. The source code of the formalisation can be found in the folder `src`.
2. The library is organized by mathematical subject, with one folder per mathematical subject. For each folder, there is also an Agda file of the same name, which lists the files in that folder by importing them publicly.
3. The `agda-unimath` library has the goal to be an informative resource of formalised mathematics. We therefore formalise in literate agda, using markdown. We think of the files in the formalisation as pages of a wiki on mathematics.
4. The files focus sharply on one topic. Typically, a file begins by introducing one new concept, possibly in several equivalent ways, and developing the most basic properties thereof. Alternatively, a file could have the goal to prove an important theorem, and derive immediate corollaries thereof.

## The design philosophy of `agda-unimath`

When a human is looking for something in a library of formalized mathematics, they likely have a clear idea of what concept they are looking for. It would be unlikely, however, that they know exactly what other concepts the concept they are looking for depends on. If the concept they're looking for is an instance of something more general, we also cannot count on it that they know about that this is the case. Certainly, we wouldn't require humans to know anything at all about _how_ their concept has been formalized in order to find it in `agda-unimath`. In fact, Humans might not yet know very much about the concept they're looking for except the name, and they might have come to find more information about it. The best case scenario for someone like that is that they can readily find their concept being listed in a hyperlinked index, like the index in the back of a book, so that they can find it there, click on it, and find what they were looking for.

Concepts are made prominent in the `agda-unimath` library because humans know how to look for them. An index of the concepts formalized in `agda-unimath` is formed by the list of files in the library, and the indexing terms are the file names. Since we want to help humans to easily find the topics they're interested in, all the files in our library are narrowly focused on one concept, on one named theorem or on one specific topic. The file names describe that concept, theorem, or topic in a concise and natural manner.

This choice of organization of the library implies that we can organize our files much like pages on a wiki. The title of the file is the topic at hand, in an informal section we can describe in words what the main idea is; then we give the main definition, the basic infrastructure around it, and we derive properties or consequences that hold in the same generality as the main definition of the file.

For example, the file about sets defines first what a set is, and then goes on to show that sets are closed under equivalences, dependent pair types, dependent product types, and so on. But it doesn't show that the type of natural numbers is a set because users would more likely expect such a fact to be presented on the page about natural numbers.

Now we can do a thought experiment. Suppose we have an unorganized library of mathematics, and we organize everything by topic as described above. Mathematics is already a well-organised subject, so for most of the library this is our preferred way to organise it. But at the bottom of the library we will find a cluster of interdependent files, and Agda will give errors because of those cyclic dependencies. This is because our desire to organise the library by topic doesn't take the bootstrapping process of getting things off the ground at the foundational level of the library.

To resolve those cyclic dependencies, we created two folders for the foundation of the `agda-unimath` library: the `foundation-core` folder containing the basic setup, and the `foundation` folder, containing everything that belongs to the foundation of the library. The `foundation-core` folder contains files that are paired with files of the same name in the `foundation` folder. The corresponding file in the `foundation` folder imports this file from the `foundation-core` folder publicly. Users who are working in areas outside of the foundation can just import files directly from `foundation`, and they don't have to worry that some files might be split in two.

Outside of the `foundation` folder of the library, we stick to the "one-concept-per-file" design principle of our library. If you find, however, that something you were looking for was not in the place you expected it to be (this happens!) please let us know and we will consider it for improvements.
